Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Equivalence.
Require Import Hylo.Morphism.
Require Import Hylo.Container.
Require Import Hylo.Coalgebra.

From Stdlib Require Extraction.

Section FCoalgDef.
  Context `(F : Cont Sh P).

  Inductive RecF `{eA : setoid A} (h : Coalg F A) : A -> Prop :=
  | RecF_fold x : (forall e, RecF h (cont (h x) e)) -> RecF h x.
  Hint Constructors RecF : ffix.

  Lemma RecF_inv `{eA : setoid A} (h : Coalg F A) x
    : RecF h x -> forall e, RecF h (cont (h x) e).
  Proof. intros []. auto. Defined.

  Lemma ext_eq_fin `(eA : setoid A) (c0 c1 : A ~> App F A) (H : c0 =e c1)
    (x y : A) (H0 : x =e y) : RecF c0 x -> RecF c1 y.
  Proof.
    intros f; revert c1 y H H0; induction f as [x H' Ih]; intros c1 y H H0.
    constructor; intros e.
    assert (Exy : c0 x =e c1 y) by (rewrite H, H0; reflexivity).
    destruct Exy as [Sxy Kxy]; symmetry in Sxy.
    destruct (elem_valid_irr Sxy e) as [e' Hv].
    apply (Ih e'); trivial; apply Kxy; symmetry; trivial.
  Qed.

  Add Parametric Morphism `{eA : setoid A} : (@RecF A eA)
      with signature
      (eqRel (A:=Coalg F A))
        ==> (eqRel (A:=A))
        ==> (eqRel (A:=Prop))
        as finMorphism.
  Proof. split; apply ext_eq_fin; trivial; symmetry; trivial. Qed.

  Definition RecP `{eA : setoid A} (c : Coalg F A) := forall x, RecF c x.

  Add Parametric Morphism `{eA : setoid A} : (@RecP A eA)
    with signature
    (eqRel (A := Coalg F A))
      ==> (eqRel (A:=Prop))
      as RecPMorphism.
  Proof.
    intros f g H; split; intros Pf x; [rewrite <- H | rewrite H]; trivial.
  Qed.

  Structure RCoalg `{eA : setoid A} :=
    Rec {
        coalg :> Coalg F A;
        recP : RecP coalg
      }.
  Arguments RCoalg A {eA}.
  Arguments Rec {A eA} coalg recP.

  #[export] Instance equiv_rcoalg `{setoid A} : setoid (RCoalg A).
  Proof.
    refine {| eqRel := fun x y => coalg x =e coalg y |}; auto with ffix.
    intros x y z H1 H2; transitivity y; auto with ffix.
  Defined.
  #[export] Instance rcoalg_no_def_eq `{setoid A} : NoDefEq (RCoalg A) := {}.

  Lemma terminating `{setoid A} : forall (h : RCoalg A) x, RecF h x.
  Proof. destruct h. trivial. Defined.

  Definition respects_relation `{eA : setoid A} (c : Coalg F A)
    {B} (m : A -> B) (R : B -> B -> Prop)
    := forall x (p : Pos F (shape (c x))), R (m (cont (c x) p)) (m x).

  Lemma wf_coalg_rec `{setoid A} {B}
    (m : A -> B) (R : B -> B -> Prop) (WF : well_founded R)
    (c : Coalg F A) (RR : respects_relation c m R) : RecP c.
  Proof.
    intros x. specialize (WF (m x)). revert x WF.
    fix Ih 2. intros x [Fx]. constructor. intros e.
    apply Ih, Fx, RR.
  Defined.
  Arguments wf_coalg_rec {A eA B m R} WF {c} RR : rename.

  Definition mk_wf_coalg `{eA : setoid A}
    {B} (m : A -> B) (R : B -> B -> Prop) (WF : well_founded R)
    (c : Coalg F A) (RR : respects_relation c m R) : RCoalg A :=
    Rec c (wf_coalg_rec WF RR).
  Arguments mk_wf_coalg {A}%_type_scope {eA} {B}%_type_scope m [R] WF [c]
    RR.

  (** The converse: a recursive coalgebra is well-founded for the relation
    * "is a child of", so its termination proofs can be used where
    * [well_founded] is expected. *)
  Definition child `{eA : setoid A} (c : Coalg F A) (y x : A) : Prop :=
    exists e : Pos F (shape (c x)), cont (c x) e = y.

  Lemma RecF_Acc `{eA : setoid A} (c : Coalg F A) x
    : RecF c x <-> Acc (child c) x.
  Proof.
    split; induction 1 as [x _ Ih]; constructor.
    - intros y [e <-]; apply Ih.
    - intros e; apply Ih; exists e; reflexivity.
  Qed.

  Lemma RecP_well_founded `{eA : setoid A} (c : Coalg F A)
    : RecP c <-> well_founded (child c).
  Proof. split; intros H x; apply RecF_Acc, H. Qed.

  (* Finite Trees *)
  Definition FinF : GFix F -> Prop := RecF g_out.

  Lemma ana_rcoalg_fin `{setoid A} (c : Coalg F A) (Rc : RecP c)
    : forall x, FinF (ana c x).
  Proof.
    intros x; induction (Rc x) as [x _ Ih]; constructor; exact Ih.
  Qed.

  Lemma fin_ana_rcoalg `{setoid A}
    (h : Coalg F A) (FT : forall x, FinF (ana h x)) : RecP h.
  Proof.
    intros x; specialize (FT x); revert FT.
    generalize (eq_refl (ana h x)); generalize (ana h x) at -1.
    intros g Eg HF; revert x Eg; induction HF as [g _ Ih]; intros x Eg; subst.
    constructor; intros e; apply (Ih e _ eq_refl).
  Qed.

  Corollary ana_rec_term `{setoid A} (h : Coalg F A)
    : (forall x, FinF (ana h x)) <-> RecP h.
  Proof. split; [apply fin_ana_rcoalg | apply ana_rcoalg_fin]. Qed.

  Corollary rcoalg_fin `{setoid A} (h : RCoalg A) : forall x, FinF (ana h x).
  Proof. apply ana_rcoalg_fin. destruct h; trivial. Qed.

End FCoalgDef.
Arguments RCoalg {Sh Esh P} F A {eA}.

(** A coalgebra [c] can be used where an [RCoalg] is expected once a canonical
  * [RCoalg] for it is declared, e.g.
  * [Canonical Structure c_rec := Rec (proof : RecP c)].
  * Rocq then inserts [reverse_coercion], which extraction inlines. *)
Extraction Inline reverse_coercion.

Section CAlgDef.
  Context `{F : Cont Sh P}.

  Definition lg_out_ (x : GFix F | FinF x) : App F {x : GFix F | FinF x}
    := let hx := g_out (proj1_sig x) in
       MkCont (shape hx)
         (fun e => exist (fun ex => _) (cont hx e) (RecF_inv (proj2_sig x) e)).

  Lemma lg_out_arr : forall x y, x =e y -> lg_out_ x =e lg_out_ y.
  Proof.
    intros [x Fx] [y Fy] Rxy; destruct (GFixR_unfold Rxy); split; trivial.
  Qed.

  Definition lg_out : {x : GFix F | FinF x} ~> App F {x : GFix F | FinF x}
    := MkMorph lg_out_arr.

  Definition lg_in_ (x : App F {g : GFix F | FinF g}) : {x : GFix F | FinF x}
    := let gx := g_in (MkCont (shape x) (fun e => proj1_sig (cont x e))) in
       exist (fun g => _) gx
         (RecF_fold
            (fun e : Pos F (shape (g_out gx)) => proj2_sig (cont x e))).

  Lemma lg_in_arr : forall x y, x =e y -> lg_in_ x =e lg_in_ y.
  Proof. intros [Sx Kx] [Sy Ky] [Sxy Kxy]; apply GFixR_in; trivial. Qed.

  Definition lg_in : App F {g : GFix F | FinF g} ~> {x : GFix F | FinF x}
    := MkMorph lg_in_arr.

  Lemma lg_in_out : lg_in \o lg_out =e id.
  Proof.
    intros [g Pg]; apply GFixR_in; [reflexivity|].
    intros e1 e2 Hv; simpl; rewrite (elem_val_eq Hv); apply GFixR_refl.
  Qed.

  Lemma lg_out_in : lg_out \o lg_in =e id.
  Proof.
    intros [Sx Kx]; constructor; [reflexivity|].
    intros e1 e2 Hv; simpl; rewrite (elem_val_eq Hv); apply GFixR_refl.
  Qed.

  Lemma lg_out_rec : RecP lg_out.
  Proof.
    intros [x Fx]; revert x Fx; fix Ih 2; intros x [x' Fx]; constructor; intros e.
    exact (Ih _ (Fx e)).
  Defined.

  Definition lg_out_c : RCoalg F {x : GFix F | FinF x} := Rec (coalg := lg_out) lg_out_rec.
End CAlgDef.


Lemma f_comp_eta_rec `{F : Cont Sf Pf} {Pg} {G : Cont Sf Pg}
  `{setoid X} `{setoid Y} `{setoid A} (f : X ~> Y) (c : RCoalg (Nest F G X) A)
  : RecP (cmap f \o c).
Proof.
  intros x; induction (terminating c x) as [x _ Ih].
  constructor; with_strategy opaque [cmap] (simpl in *).
  unfold cmap at 1 4; with_strategy opaque [cmap] simpl.
  destruct (c x) as [[sx kx] kx']; simpl in *; intros [v V]; simpl in *.
  apply Ih.
Defined.

Lemma f_nat_eta_rec `{F : Cont Sf P} `{setoid Sg} {G : Cont Sg P} `{setoid A}
  (f : naturalM F G) (c : RCoalg F A) : RecP (natural f \o c).
Proof.
  intros x; induction (terminating c x) as [x _ Ih]; constructor; simpl in *.
  destruct (c x) as [sx kx]; simpl in *; intros [v V]; apply Ih.
Defined.

Canonical Structure f_nat_eta `{F : Cont Sf P} `{setoid Sg} {G : Cont Sg P}
  `{setoid A} (f : naturalM F G) (c : RCoalg F A) : RCoalg G A
  := Rec (coalg := natural f \o c) (f_nat_eta_rec f c).

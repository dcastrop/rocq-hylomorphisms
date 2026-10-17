Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Equivalence.
Require Import Hylo.Morphism.
Require Import Hylo.Container.
Require Import Hylo.Algebra.
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

  Lemma fin_out : forall x, RecF l_out x.
  Proof. induction x as [s Ih]. constructor. apply Ih. Defined.

  Canonical Structure f_out : RCoalg (LFix F) := Rec _ fin_out.

  Definition rana_f__ `{setoid A} (c : Coalg F A)
    : forall x : A, RecF c x -> LFix F :=
    fix f (x : A) (H : RecF c x) :=
      let hx := c x in
      LFix_in (MkCont (shape hx) (fun e => f (cont hx e) (RecF_inv H e))).
  Arguments rana_f__ {A eA} c x H : rename.

  Lemma rana_f_irr `{eA : setoid A} (h : Coalg F A)
    : forall (x : A) (F1 F2 : RecF h x), rana_f__ h x F1 =e rana_f__ h x F2.
  Proof.
    fix Ih 2; intros x0 [x Fx] F2; clear x0; destruct F2 as [x Fy].
    split; [reflexivity|]; intros e1 e2 d; rewrite (elem_val_eq d); apply Ih.
  Qed.

  Definition rana_f_ `{eA : setoid A} (c : RCoalg A) x
    := rana_f__ c x (terminating c x).

  Lemma rana_f_arr `{eA : setoid A} (h : RCoalg A)
    : forall x y, x =e y -> rana_f_ h x =e rana_f_ h y.
  Proof.
    intros x y; unfold rana_f_.
    generalize (terminating h x) (terminating h y); revert x y.
    fix Ih 3; intros x y [x' Fx] [y' Fy] Hxy; simpl in *.
    destruct (app_eq h Hxy); split; auto; intros; apply Ih; auto.
  Qed.

  Definition rana_f `{eA : setoid A} (c : RCoalg A) : A ~> LFix F
    := Eval unfold rana_f_, rana_f__ in MkMorph (rana_f_arr c).

  Lemma rana_arr `{eA : setoid A}
    : forall x y : RCoalg A, x =e y -> rana_f x =e rana_f y.
  Proof.
    intros f g Efg x; simpl.
    generalize (terminating f x) (terminating g x); intros Fx.
    generalize (e_refl x); generalize x at 2 3 5; intros y Ey Fy.
    revert x Fx y Fy Ey; fix Ih 2.
    intros x' [x Fx] y' [y Fy] Exy; clear x' y'; simpl.
    assert (He : f x =e g y) by (rewrite Exy; apply Efg).
    destruct He as [Sxy Kxy]; split; trivial.
    intros e1 e2 Hv; apply Ih, Kxy, Hv.
  Qed.

  Definition rana `{eA : setoid A} : RCoalg A ~> A ~> LFix F
    := Eval unfold rana_f in MkMorph rana_arr.

  Lemma LFixR_fold (x y : LFix F) : LFixR x y = (x =e y).
  Proof. auto. Qed.

  Lemma rana_univ_r A (eA : setoid A) (h : RCoalg A) (f : A ~> LFix F)
    : f =e l_in \o fmap f \o h -> f =e rana h.
  Proof.
    intros H; unfold rana; simpl; intros x; generalize (terminating h x).
    revert x; fix Ih 2; intros x0 [x Fx]; clear x0.
    rewrite LFixR_fold, (H _); simpl; split; [reflexivity|].
    intros d1 d2 e; rewrite (elem_val_eq e); apply Ih.
  Qed.

  Lemma rana_univ_l A {eA : setoid A} (h : RCoalg A) (f : A ~> LFix F)
    : f =e rana h -> f =e l_in \o fmap f \o h.
  Proof.
    intros H x0; rewrite (H _); simpl; unfold rana.
    generalize (terminating h x0) as Fx; intros [x Fx]; clear x0; simpl.
    split; [reflexivity|]; intros d1 d2 e; rewrite (elem_val_eq e).
    generalize (H (cont (coalg h x) d2)); simpl; rewrite !LFixR_fold.
    intros ->; apply rana_f_irr.
  Qed.

  Lemma rana_univ A {eA : setoid A} (h : RCoalg A) (f : A ~> LFix F)
    : f =e rana h <-> f =e l_in \o fmap f \o h.
  Proof. split;[apply rana_univ_l|apply rana_univ_r]. Qed.

  Corollary rana_unfold A {eA : setoid A} (h : RCoalg A)
    : rana h =e l_in \o fmap (rana h) \o h.
  Proof. rewrite <- rana_univ. reflexivity. Qed.
End FCoalgDef.
Arguments RCoalg {Sh Esh P} F A {eA}.

(** A coalgebra [c] can be used where an [RCoalg] is expected once a canonical
  * [RCoalg] for it is declared, e.g.
  * [Canonical Structure c_rec := Rec (proof : RecP c)].
  * Rocq then inserts [reverse_coercion], which extraction inlines. *)
Extraction Inline reverse_coercion.

Arguments rana & {Sh}%_type_scope {Esh} {P}%_type_scope {F}
  {A}%_type_scope {eA}.

Arguments f_out & {Sh}%_type_scope {Esh} {P}%_type_scope {F}.

Section CAlgDef.
  Context `{F : Cont Sh P}.

  Definition ccata_f_ `{eA : setoid A} (g : Alg F A)
    : forall x : GFix F, FinF x -> A
    := fix f x H :=
      let hx := g_out x in
      g (MkCont (shape hx) (fun e => f (cont hx e) (RecF_inv H e))).

  Lemma ccata_f_irr `{eA : setoid A} (h : Alg F A)
    : forall x (F1 F2 : FinF x), ccata_f_ h F1 =e ccata_f_ h F2.
  Proof.
    fix Ih 2; intros x F1 F2; destruct F1 as [x F1]; destruct F2 as [x F2].
    apply app_eq; split; [reflexivity|].
    intros e1 e2 Hv; simpl; rewrite (elem_val_eq Hv); apply Ih.
  Qed.

  Definition ccata_f `{eA : setoid A} (g : Alg F A)
    : {x : GFix F | FinF x} -> A
    := fun x => ccata_f_ g (proj2_sig x).

  Lemma ccata_arr1 `{eA : setoid A} (g : Alg F A)
    : forall x y, x =e y -> ccata_f g x =e ccata_f g y.
  Proof.
    intros [x Fx] [y Fy] Rxy; simpl in *; unfold ccata_f; simpl.
    revert x y Fx Fy Rxy; fix Ih 3; intros x y [x' Fx] [y' Fy] Rxy.
    apply GFixR_unfold in Rxy; destruct Rxy as [ES EK].
    apply app_eq; split; trivial; intros e1 e2 Hv; apply Ih, EK, Hv.
  Qed.

  Definition ccata_ `{eA : setoid A} g : {x : GFix F | FinF x} ~> A
    := MkMorph (ccata_arr1 g).

  Lemma ccata_arr `{eA : setoid A}
    : forall x y : Alg F A, x =e y -> ccata_ x =e ccata_ y.
  Proof.
    intros x y Hxy [g Fg]; unfold ccata_, ccata_f; simpl.
    revert g Fg; fix Ih 2; intros g [ES EK]; simpl.
    rewrite Hxy; apply app_eq; constructor; simpl; auto with ffix.
    intros e1 e2 Hv; rewrite (elem_val_eq Hv); apply Ih.
  Qed.

  Definition ccata `{eA : setoid A} : Alg F A ~> {x : GFix F | FinF x} ~> A
    := MkMorph ccata_arr.

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

  Lemma ccata_univ_r `{eA : setoid A} (g : Alg F A)
    (f : {x : GFix F | FinF x} ~> A)
    : f =e g \o fmap f \o lg_out -> f =e ccata g.
  Proof.
    intros H [e Fe]; simpl; unfold ccata_f; simpl.
    revert e Fe; fix Ih 2; intros e Fe; destruct Fe as [e Fe].
    rewrite H; simpl; apply app_eq; constructor; [reflexivity|].
    intros e1 e2 Hv; simpl; rewrite (elem_val_eq Hv); apply Ih.
  Qed.

  Lemma ccata_univ_l `{eA : setoid A} (g : Alg F A)
    (f : {x : GFix F | FinF x} ~> A)
    : f =e ccata g -> f =e g \o fmap f \o lg_out.
  Proof.
    intros -> [x Fx]; destruct Fx as [x Fx]; reflexivity.
  Qed.

  Lemma ccata_univ `{eA : setoid A} (g : Alg F A)
    (f : {x : GFix F | FinF x} ~> A)
    : f =e ccata g <-> f =e g \o fmap f \o lg_out.
  Proof. split;[apply ccata_univ_l|apply ccata_univ_r]. Qed.

  Corollary ccata_unfold `{eA : setoid A} (g : Alg F A)
    : ccata g =e g \o fmap (ccata g) \o lg_out.
  Proof. rewrite <- ccata_univ. reflexivity. Qed.

  Lemma ccata_in_id : ccata lg_in =e id.
  Proof.
    symmetry; apply ccata_univ; rewrite fmap_id, idKr, lg_in_out; reflexivity.
  Qed.
End CAlgDef.

Section FinRec.
  Context `{F : Cont Sh P}.

  Lemma cata_ccata `{setoid A} (f : Alg F A) : cata f \o ccata l_in =e ccata f.
  Proof.
    apply ccata_univ.
    rewrite fmap_comp.
    ainsert (l_out_in (F:=F)) before (fmap (F:=F) (ccata (l_in (F:=F)))).
    arewrite <- (cata_unfold f); arewrite <- (ccata_unfold (l_in (F:=F))).
    reflexivity.
  Qed.

  Lemma ccata_cata `{setoid A} (f : Alg F A) : ccata f \o cata lg_in =e cata f.
  Proof.
    apply cata_univ.
    rewrite fmap_comp.
    ainsert (lg_out_in (F:=F)) before (fmap (F:=F) (cata (lg_in (F:=F)))).
    arewrite <- (ccata_unfold f); arewrite <- (cata_unfold (lg_in (F:=F))).
    reflexivity.
  Qed.

  Definition f_to_fg : LFix F ~> {x : GFix F | FinF x} := cata lg_in.
  Definition fg_to_f : {x : GFix F | FinF x} ~> LFix F := ccata l_in.

  Corollary fg_to_fI : fg_to_f \o f_to_fg =e id.
  Proof. unfold fg_to_f, f_to_fg; rewrite <- cata_in_id; apply ccata_cata. Qed.

  Corollary f_to_fgI : f_to_fg \o fg_to_f =e id.
  Proof.
    unfold fg_to_f, f_to_fg; rewrite <- ccata_in_id; apply cata_ccata.
  Qed.

  Lemma ccata_ana_r `{setoid A}
    (f : A ~> GFix F) (Ff : forall x, FinF (f x)) (g : A ~> LFix F)
    : ccata l_in \o liftP f Ff =e g -> f =e ana l_out \o g.
  Proof.
    unfold liftP, liftP_f_, ccata_f; simpl; intros Hx x.
    specialize (Hx x); generalize dependent (Ff x); generalize (g x) (f x).
    clear Ff f g x; intros l; induction l as [l Ih]; intros y Fy.
    destruct Fy as [y Fy].
    simpl in *; intros [Sfg Rk]; apply GFixR_in; trivial.
    intros e1 e2 Hv; apply Ih with (f:=Fy e1), Rk, Hv.
  Qed.

  Lemma ccata_ana_l `{setoid A}
    (f : A ~> GFix F) (Ff : forall x, FinF (f x)) (g : A ~> LFix F)
    : f =e ana l_out \o g -> ccata l_in \o liftP f Ff =e g.
  Proof.
    unfold liftP, liftP_f_, ccata_f; simpl; intros Hx x.
    specialize (Hx x); revert Hx; generalize (g x) (f x) (Ff x).
    clear f Ff g x; induction l as [l Ih]; intros g Fg; destruct Fg as [g Fg].
    intros Hg; simpl in *.
    apply GFixR_unfold in Hg; destruct Hg as [Sg Kg]; split; trivial.
    intros e1 e2 Hv; apply Ih, Kg, Hv.
  Qed.

  Lemma ccata_ana `{setoid A}
    (f : A ~> GFix F) (Ff : forall x, FinF (f x)) (g : A ~> LFix F)
    : f =e ana l_out \o g <-> ccata l_in \o liftP f Ff =e g.
  Proof. split; [apply ccata_ana_l| apply ccata_ana_r]. Qed.

  Lemma rana_ana `{setoid A} (f : RCoalg F A) : ana f =e ana l_out \o rana f.
  Proof.
    symmetry; apply ana_univ.
    rewrite fmap_comp; ainsert (l_out_in (F:=F)) before (fmap (F:=F) (rana f)).
    arewrite <- (ana_unfold (l_out (F:=F))); arewrite <- (rana_unfold f).
    reflexivity.
  Qed.

  Corollary ana_rana `{setoid A} (f : RCoalg F A)
    : ccata l_in \o liftP (ana f) (rcoalg_fin f) =e rana f.
  Proof. rewrite <- ccata_ana; apply rana_ana. Qed.
End FinRec.

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

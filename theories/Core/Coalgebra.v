Set Warnings "-bad-template-constraint,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

From Paco Require Import paco.
Require Import Hylo.Core.Cofix.
Require Import Hylo.Core.Equivalence.
Require Import Hylo.Core.Morphism.
Require Import Hylo.Core.Container.


Abbreviation Coalg F A := (A ~> App F A) (only parsing).

Section CoalgDef.
  Context `(F : Cont Sh P).

  Set Primitive Projections.
  CoInductive GFix : Type := GFix_in { GFix_out : App F GFix }.
  Unset Primitive Projections.

  Abbreviation gshape x := (shape (GFix_out x)).
  Abbreviation gcont x := (cont (GFix_out x)).
  Abbreviation grelT := (GFix -> GFix -> Prop) (only parsing).

  Inductive GFixR_ (G : grelT) (x y : GFix) : Prop :=
  | GFixR_in_
      (ShE : gshape x =e gshape y)
      (ElemE : forall e1 e2, val e1 = val e2 -> G (gcont x e1) (gcont y e2)).

  Definition GFixR : grelT := paco2 GFixR_ bot2.

  Lemma GFixR_in (x y : GFix) (ShE : gshape x =e gshape y)
    (ElemE : forall e1 e2, val e1 = val e2 -> GFixR (gcont x e1) (gcont y e2))
    : GFixR x y.
  Proof.
    apply paco2_fold; constructor; trivial.
    intros e1 e2 Heq; left; apply ElemE, Heq.
  Qed.
  Hint Resolve GFixR_in : ffix.

  Lemma GFixR_mon : monotone2 GFixR_.
  Proof.
    intros x y r rr [sh k] H; apply (GFixR_in_ sh); intros e1 e2 Ev.
    apply H, k, Ev.
  Qed.
  Create HintDb gfix.
  Hint Resolve GFixR_mon : gfix.

  Lemma GFixR_unfold x y (R : GFixR x y)
    : (gshape x =e gshape y) /\
        (forall e1 e2, val e1 = val e2 -> GFixR (gcont x e1) (gcont y e2)).
  Proof.
    apply paco2_unfold in R; auto with gfix; destruct R as [SE KE].
    split; trivial; intros e1 e2 Hv; destruct (KE e1 e2 Hv) as [|[]]; trivial.
  Qed.

  Lemma GFixR_refl : forall x, GFixR x x.
  Proof.
    intro x; coind CH; intros x; apply paco2_fold; constructor; [reflexivity|].
    intros e1 e2 Ev; right; rewrite (cont_valid_irrelevant Ev); apply CH.
  Qed.

  Lemma GFixR_sym : forall x y, GFixR x y -> GFixR y x.
  Proof.
    intros x y; coind CH; intros x y Gf.
    apply paco2_unfold in Gf; eauto with gfix; destruct Gf as [Hsh Hk].
    apply e_sym in Hsh; apply paco2_fold, (GFixR_in_ Hsh).
    intros e1 e2 Hv; right; apply CH.
    symmetry in Hv; destruct (Hk e2 e1 Hv) as [|[]]; trivial.
  Qed.

  Lemma GFixR_trans : forall x y z, GFixR x y -> GFixR y z -> GFixR x z.
  Proof.
    intros x y z; revert y; coind CH; intros x z y Hxy Hyz.
    apply paco2_unfold in Hxy, Hyz; eauto with gfix.
    destruct Hxy as [HxyS HxyK], Hyz as [HyzS HyzK].
    assert (HxzS : gshape x =e gshape z) by (rewrite HxyS; trivial).
    apply paco2_fold, (GFixR_in_ HxzS); intros ex ez Veq; right.
    destruct (elem_valid_irr HxyS ex) as [ey Veq2].
    assert (Veq3 : val ey = val ez) by (rewrite <- Veq2; trivial).
    apply (CH (gcont x ex) (gcont z ez) (gcont y ey)); [
        destruct (HxyK ex ey Veq2) as [|[]]
      | destruct (HyzK ey ez Veq3) as [|[]]]; trivial.
  Qed.

  #[export] Instance GFix_Eq : setoid GFix :=
    {| eqRel := GFixR;
      e_refl := GFixR_refl;
      e_sym := GFixR_sym;
      e_trans := GFixR_trans;
    |}.
  #[export] Instance GFix_no_def_eq : NoDefEq GFix := {}.

  Lemma l_in_eq (x y : App F GFix) : x =e y -> GFix_in x =e GFix_in y.
  Proof. simpl. intros []; auto with ffix. Qed.

  Lemma g_out_eq (x y : GFix) : x =e y -> GFix_out x =e GFix_out y.
  Proof.
    intros Gf; apply paco2_unfold in Gf; auto with gfix.
    destruct Gf as [ShE ElemE]; constructor; trivial.
    intros e1 e2 Veq; destruct (ElemE e1 e2 Veq) as [Gf|[]]; trivial.
  Qed.

  Abbreviation Alg F A := (App F A ~> A) (only parsing).

  Definition gfix_in : Alg F GFix := MkMorph l_in_eq.
  Definition gfix_out : Coalg F GFix := MkMorph g_out_eq.

  Lemma gfix_in_out : gfix_in \o gfix_out =e id (A:=GFix).
  Proof.
    intros x; apply paco2_fold; constructor; auto with ffix.
    intros e1 e2 Ev; left; simpl; rewrite (elem_val_eq Ev); apply GFixR_refl.
  Qed.

  Lemma gfix_out_in : gfix_out \o gfix_in =e id (A:=App F GFix).
  Proof. simpl. intros. generalize (e_refl x). simpl. trivial. Qed.

  Definition ana_f_u `{setoid A} (c : Coalg F A) (gf : A -> GFix) (x : A) :=
    let cx := c x in MkCont (shape cx) (fun e => gf (cont cx e)).

  Definition ana_f_ `{setoid A} (c : Coalg F A)
    := cofix f x := GFix_in (ana_f_u c f x).

  Lemma unfold_ana_f `{setoid A} (c : Coalg F A) x
    : GFix_out (ana_f_ c x) = ana_f_u c (ana_f_ c) x.
  Proof. reflexivity. Qed.

  Lemma ana_f_arr `{eA : setoid A} (c : Coalg F A)
    : forall x y, x =e y -> ana_f_ c x =e ana_f_ c y.
  Proof.
    coind CH; intros x y Exy; apply paco2_fold.
    assert (Rxy : c x =e c y) by (rewrite Exy; reflexivity).
    destruct Rxy as [Es Ek]; constructor; trivial.
    intros e1 e2 Hv; right; apply CH, Ek, Hv.
  Qed.

  Definition ana_f `(eA : setoid A) (c : Coalg F A) : A ~> GFix
    := MkMorph (ana_f_arr c).

  Lemma ana_arr `{eA : setoid A}
    : forall x y : Coalg F A, x =e y -> ana_f x =e ana_f y.
  Proof.
    intros f g Hfg x; generalize (e_refl x); generalize x at 2 4.
    intros y Hxy; revert f g Hfg x y Hxy; coind CH; intros f g He x y Hxy.
    assert (Rfg : f x =e g y) by (rewrite Hxy; apply He).
    destruct Rfg as [Es Ek]; apply paco2_fold; constructor; trivial.
    intros e1 e2 Hv; right; apply CH, Ek, Hv; trivial.
  Qed.

  Definition gfix_ana `{eA : setoid A} : Coalg F A ~> A ~> GFix :=
    MkMorph ana_arr.

  Lemma gfix_ana_univ `{eA : setoid A} (h : Coalg F A) (f : A ~> GFix)
    : f =e gfix_ana h <-> f =e gfix_in \o fmap f \o h.
  Proof.
    split.
    - intros H; rewrite H; intros x; apply paco2_fold; constructor;
        simpl; [reflexivity|].
      intros e1 e2 Hv; rewrite (elem_val_eq Hv); left; apply GFixR_refl.
    - intros He x; simpl.
      generalize (e_refl (f x)); generalize (f x) at 1 3; revert x.
      coind CH; intros g0 x Ef.
      assert (Rfg : g0 =e gfix_in (fmap f (h x))) by (rewrite Ef; apply He).
      apply paco2_unfold in Rfg; auto with gfix; destruct Rfg as [Es Ek].
      simpl in Es, Ek; apply paco2_fold; constructor; trivial.
      intros e1 e2 Hv; right; apply CH; destruct (Ek e1 e2 Hv) as [|[]];
        trivial.
  Qed.
End CoalgDef.

(** * Terminal coalgebras
  *
  * Dual to [Initial] (in [Algebra]): [T] is a terminal [F]-coalgebra, with
  * [g_out] and its inverse [g_in]. [GFix F] is the default one. *)
#[mode = "- - - - - -"]
Class Terminal `(F : Cont Sh P) (T : Type) `{eT : setoid T} :=
  { g_in : App F T ~> T;
    g_out : T ~> App F T;
    g_in_out : g_in \o g_out =e id;
    g_out_in : g_out \o g_in =e id;
    ana : forall `{eA : setoid A}, Coalg F A ~> A ~> T;
    ana_univ : forall `{eA : setoid A} (h : Coalg F A) (f : A ~> T),
        f =e ana h <-> f =e g_in \o fmap f \o h
  }.

Arguments Terminal {Sh Esh P} F T {eT}.
Arguments g_in & {Sh Esh P F T eT _}.
Arguments g_out & {Sh Esh P F T eT _}.
Arguments ana {Sh Esh P F T eT _ A eA}.
Arguments g_in_out {Sh Esh P F T eT _}.
Arguments g_out_in {Sh Esh P F T eT _}.
Arguments ana_univ {Sh Esh P F T eT _ A eA} h f.

#[export] Instance GFix_terminal `(F : Cont Sh P) : Terminal F (GFix F) | 1 :=
  {| g_in := gfix_in F;
     g_out := gfix_out F;
     g_in_out := gfix_in_out (F := F);
     g_out_in := gfix_out_in (F := F);
     ana := fun _ _ => gfix_ana F;
     ana_univ := fun _ _ => gfix_ana_univ (F := F)
  |}.

Section TerminalLaws.
  Context `{F : Cont Sh P} `{eT : setoid T} `{!Terminal F T}.

  Lemma ana_univ_r `{eA : setoid A} (h : Coalg F A) (f : A ~> T)
    : f =e g_in \o fmap f \o h -> f =e ana h.
  Proof. apply ana_univ. Qed.

  Lemma ana_univ_l `{eA : setoid A} (h : Coalg F A) (f : A ~> T)
    : f =e ana h -> f =e g_in \o fmap f \o h.
  Proof. apply ana_univ. Qed.

  Corollary ana_unfold `{eA : setoid A} (h : Coalg F A)
    : ana h =e g_in \o fmap (ana h) \o h.
  Proof. rewrite <- ana_univ. reflexivity. Qed.

  Lemma ana_out `{eA : setoid A} (h : Coalg F A)
    : g_out \o ana h =e fmap (ana h) \o h.
  Proof.
    intros x; cbn [app comp]; rewrite (ana_unfold h x); exact (g_out_in _).
  Qed.

  Lemma ana_uniq `{eA : setoid A} (h : Coalg F A) (f : A ~> T)
    : g_out \o f =e fmap f \o h -> f =e ana h.
  Proof.
    intros Hf; apply ana_univ; intros x; cbn [app comp].
    rewrite <- (Hf x); symmetry; exact (g_in_out _).
  Qed.

  Lemma ana_out_id : ana g_out =e id (A := T).
  Proof.
    symmetry; apply ana_univ; rewrite fmap_id, idKr, g_in_out; reflexivity.
  Qed.
End TerminalLaws.
Arguments ana_out_id {Sh Esh P F} T {eT _} _.

(** Any two terminal coalgebras are isomorphic *)
Section TerminalIso.
  Context `{F : Cont Sh P} `{eT : setoid T} `{!Terminal F T}
    `{eU : setoid U} `{!Terminal F U}.

  Definition coiso : T ~> U := ana g_out.

  Lemma coiso_out : g_out \o coiso =e fmap coiso \o g_out.
  Proof. apply ana_out. Qed.

  (** Anamorphisms do not depend on the terminal coalgebra *)
  Lemma ana_coiso `{eA : setoid A} (h : Coalg F A) : coiso \o ana h =e ana h.
  Proof.
    apply ana_uniq; intros x; etransitivity; [apply (coiso_out _)|].
    cbn [app comp].
    etransitivity; [apply app_eq, (ana_out h x)|]; reflexivity.
  Qed.
End TerminalIso.
Arguments coiso {Sh Esh P F} T {eT _} U {eU _}.
Arguments coiso_out {Sh Esh P F} T {eT _} U {eU _} _.
Arguments ana_coiso {Sh Esh P F} T {eT _} U {eU _} {A eA} h _.

Lemma coiso_inv `{F : Cont Sh P} `{eT : setoid T} `{!Terminal F T}
  `{eU : setoid U} `{!Terminal F U}
  : coiso U T \o coiso T U =e id.
Proof.
  rewrite <- (ana_out_id T); apply ana_uniq; intros x; cbn [app comp].
  etransitivity; [apply (coiso_out U T _)|]; cbn [app comp].
  etransitivity; [apply app_eq, (coiso_out T U x)|]; reflexivity.
Qed.
Arguments coiso_inv {Sh Esh P F} T {eT _} U {eU _} _.

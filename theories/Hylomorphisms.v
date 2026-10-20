Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import Hylo.Equivalence.
Require Import Hylo.Morphism.
Require Import Hylo.Container.
Require Import Hylo.Coalgebra.
Require Import Hylo.FCoalgebra.

Abbreviation Alg F A := (App F A ~> A).

Section HyloDef.
  Context `{F : Cont Sh P} `{eA : setoid A} `{eB : setoid B}.

  Definition hylo_def (a : Alg F B) (c : Coalg F A)
    : forall (x : A), RecF c x -> B :=
    fix f x H :=
      match c x as cx
            return (forall e : Pos F (shape cx), RecF c (cont cx e)) -> B
      with
      | MkCont sx cx =>
          fun H => a (MkCont sx (fun e => let ce := cx e in f ce (H e)))
      end (RecF_inv H).
  Arguments hylo_def a c x H : clear implicits.

  Lemma hylo_def_irr (g : Alg F B) (h : Coalg F A)
    : forall (x : A) (F1 F2 : RecF h x),
      hylo_def g h x F1 =e hylo_def g h x F2.
  Proof.
    fix Ih 2; intros x0 [x Fx] F2; clear x0; destruct F2 as [x Fy]; simpl.
    generalize dependent (h x); clear x; intros [s_x c_x] Fx Fy; simpl in *.
    apply app_eq; split; [reflexivity|]; intros d1 d2 e.
    rewrite (elem_val_eq e); apply Ih.
  Qed.

  Definition hylo_f__ (g : Alg F B) (h : RCoalg F A)
    := Eval unfold hylo_def in fun x => hylo_def g h x (terminating h x).

  Lemma hylo_f___arr (a0 a1 : Alg F B) (c0 c1 : RCoalg F A)
    (Ea : a0 =e a1) (Ec : c0 =e c1)
    : forall x y, x =e y -> hylo_f__ a0 c0 x =e hylo_f__ a1 c1 y.
  Proof.
    unfold hylo_f__; intros x y.
    generalize (terminating c0 x), (terminating c1 y); revert x y.
    fix Ih 3; intros x y Fx Fy H; destruct Fx as [x Fx], Fy as [y Fy]; simpl.
    assert (Cxy : c0 x =e c1 y) by (rewrite H; apply Ec).
    destruct (c0 x) as [sx kx], (c1 y) as [sy ky], Cxy as [Sxy Kxy].
    simpl in *; rewrite Ea; apply app_eq; split; simpl; auto.
  Qed.

  Definition hylo_f_ (g : Alg F B) (h : RCoalg F A)
    : A ~> B := Eval unfold hylo_f__ in
      MkMorph (hylo_f___arr (e_refl g) (e_refl h)).

  Lemma hylo_f__arr (a : Alg F B)
    : forall x y, x =e y -> hylo_f_ a x =e hylo_f_ a y.
  Proof. intros x y h v; apply hylo_f___arr; auto with ffix. Qed.

  Definition hylo_f (g : Alg F B)
    : RCoalg F A ~> A ~> B :=
    Eval unfold hylo_f_ in MkMorph (hylo_f__arr g).

  Lemma hylo_f_arr : forall x y, x =e y -> hylo_f x =e hylo_f y.
  Proof. intros x y E h v; apply hylo_f___arr; auto with ffix. Qed.

  Definition hylo : Alg F B ~> RCoalg F A ~> A ~> B :=
    Eval unfold hylo_f in MkMorph hylo_f_arr.

  Lemma hylo_uniq_r (g : Alg F B) (h : RCoalg F A) (f : A ~> B)
    : f =e g \o fmap f \o h -> f =e hylo g h.
  Proof.
    intros H x; simpl; unfold hylo_f__; generalize (terminating h x); revert x.
    fix Ih 2; intros x Fx; rewrite (H _); simpl.
    destruct Fx as [x Fx]; simpl; destruct (h x) as [s_x c_x]; simpl in *.
    apply app_eq; split; [reflexivity|]; simpl; intros d1 d2 e.
    rewrite (elem_val_eq e); apply Ih.
  Qed.

  Lemma hylo_uniq_l (g : Alg F B) (h : RCoalg F A) (f : A ~> B)
    : f =e hylo g h -> f =e g \o fmap f \o h.
  Proof.
    intros ->; intros x; simpl; unfold hylo_f__.
    destruct (terminating h x) as [x Fx]; simpl.
    destruct (h x) as [s_x c_x]; simpl in *.
    apply app_eq; split; [reflexivity|]; simpl; intros d1 d2 e.
    rewrite (elem_val_eq e); apply hylo_def_irr.
  Qed.

  Lemma hylo_uniq (g : Alg F B) (h : RCoalg F A) (f : A ~> B)
    : f =e hylo g h <-> f =e g \o fmap f \o h.
  Proof. split; [apply hylo_uniq_l | apply hylo_uniq_r]. Qed.

  Corollary hylo_unr (g : Alg F B) (h : RCoalg F A)
    : hylo g h =e g \o fmap (hylo g h) \o h.
  Proof. rewrite <- hylo_uniq; reflexivity. Qed.
End HyloDef.

Section HyloFusion.
  Context `{F : Cont Sh P}.
  Context `{eA : setoid A} `{eB : setoid B} `{eC : setoid C}.

  Lemma splitC (f1 f2 : B ~> C) (g1 g2 : A ~> B)
    : f1 =e f2 -> g1 =e g2 -> f1 \o g1 =e f2 \o g2.
  Proof. intros -> ->; reflexivity. Qed.

  Lemma hylo_fusion_l (h1 : RCoalg F A) (g1 : Alg F B) (g2 : Alg F C)
    (f2 : B ~> C) (E2 : f2 \o g1 =e g2 \o fmap f2)
    : f2 \o hylo g1 h1 =e hylo g2 h1.
  Proof.
    rewrite hylo_uniq, fmap_comp; arewrite <- E2; arewrite <- (hylo_unr g1 h1).
    reflexivity.
  Qed.

  Lemma hylo_fusion_r (h1 : RCoalg F B) (g1 : Alg F C) (h2 : RCoalg F A)
    (f1 : A ~> B) (E1 : h1 \o f1 =e fmap f1 \o h2)
    : hylo g1 h1 \o f1 =e hylo g1 h2.
  Proof.
    rewrite hylo_uniq, fmap_comp; arewrite <- E1; arewrite <- (hylo_unr g1 h1).
    reflexivity.
  Qed.

  Lemma deforest (h1 : RCoalg F A) (g2 : Alg F C)
    (g1 : Alg F B) (h2 : RCoalg F B) (INV: h2 \o g1 =e id)
    : hylo g2 h2 \o hylo g1 h1 =e hylo g2 h1.
  Proof.
    apply hylo_fusion_l; rewrite (hylo_unr g2 h2) at 1; arewrite INV.
    rewrite idKr; reflexivity.
  Qed.
End HyloFusion.

Corollary hylo_map_shift `{F : Cont Sf P} `{setoid Sg} {G : Cont Sg P}
  `{setoid A} `{setoid B}
  (g : Alg G B) (m : naturalM F G) (h : RCoalg F A)
  : hylo (g \o natural m) h =e hylo g (natural m \o h).
Proof.
  apply hylo_uniq; rewrite hylo_unr at 1.
  arewrite (natural_fmap m (hylo (g \o natural m) h)). reflexivity.
Qed.

Arguments deforest & {_ _ _ _ _ _ _ _ _ _ _ _ _ _}.

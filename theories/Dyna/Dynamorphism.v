Set Warnings "-bad-template-constraint,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Core.
Require Import Hylo.Schemes.
Require Import Hylo.Dyna.Memo.

(** * The dynamorphism
  *
  * [dyna] works for any memo table: [LFix (Memo G A)] ([LFix_initial]) is the
  * default, and [dyna_iso] replaces one by another. *)
Definition dyna `{setoid A} `{setoid B} `{G : Cont Sg Pg} `{eT : setoid T}
  `{!Initial (Memo G A) T} (a : App G T ~> A) (c : RCoalg G B) : B ~> A
  := mhead \o l_out \o hylo (l_in \o mcons \o pair a id) c.

#[export] Instance dyna_proper `{setoid A} `{setoid B} `{G : Cont Sg Pg}
  `{eT : setoid T} `{!Initial (Memo G A) T}
  : Proper (eqRel ==> eqRel ==> eqRel) (dyna (T := T) (B := B)).
Proof. intros a1 a2 Ea c1 c2 Ec; unfold dyna; rewrite Ea, Ec; reflexivity. Qed.

(** [dyna] does not depend on the memo table *)
Theorem dyna_iso `{setoid A} `{setoid B} `{G : Cont Sg Pg}
  `{eT : setoid T} `{!Initial (Memo G A) T}
  `{eU : setoid U} `{!Initial (Memo G A) U} (a : App G T ~> A) (c : RCoalg G B)
  : dyna a c =e dyna (a \o fmap (iso U T)) c.
Proof.
  unfold dyna; erewrite <- (hylo_fusion_l c (f2 := iso U T)).
  - arewrite (iso_out U T); arewrite (mhead_fmap G A (iso U T)).
    reflexivity.
  - arewrite (iso_in U T); arewrite (mcons_nat G A (iso U T)).
    intros x; reflexivity.
Qed.

(** Memoising with the same coalgebra: the algebra reads the heads of the
  * children's tables *)
Theorem dyna_heads `{setoid A} `{setoid B} `{G : Cont Sg Pg}
  `{eT : setoid T} `{!Initial (Memo G A) T}
  (a : App G A ~> A) (c : RCoalg G B)
  : hylo a c =e dyna (a \o fmap (mhead \o l_out)) c.
Proof.
  unfold dyna; symmetry; apply hylo_fusion_l; arewrite l_out_in.
  intros [s k]; reflexivity.
Qed.

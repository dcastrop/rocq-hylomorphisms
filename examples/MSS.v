Set Warnings "-bad-template-constraint,-disj-pattern-notation".
Set Warnings "-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import Hylo.Hylo.
Require Import Hylo.Lists.
Require Import Hylo.Extraction.Specialise.
Require Import Hylo.Extraction.ExtrBigint.


From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

Definition omax (x y : option Z) : option Z :=
  match x, y with
  | None, _ => y
  | _, None => x
  | Some a, Some b => Some (Z.max a b)
  end.

Definition oplus (x y : option Z) : option Z :=
  match x, y with
  | Some a, Some b => Some (a + b)
  | _, _ => None
  end.

Ltac ocases :=
  intros; repeat match goal with x : option Z |- _ => destruct x end;
  simpl; try reflexivity; try lia.

Program Definition max_monoid : Monoid (option Z) :=
  {| skip := None; par := morph_of (fun x => morph_of (omax x)) |}.
Solve All Obligations with ocases.

Program Definition plus_monoid : Monoid (option Z) :=
  {| skip := Some 0; par := morph_of (fun x => morph_of (oplus x)) |}.
Solve All Obligations with ocases.

Program Definition maxplus : Semiring (option Z) :=
  {| sadd := max_monoid; smul := plus_monoid |}.
Solve All Obligations with ocases.

Definition maximum : list (option Z) ~> option Z := reduce max_monoid id.
Definition sum : list (option Z) ~> option Z := reduce plus_monoid id.

Definition segs : list (option Z) ~> list (list (option Z)) :=
  concat \o lmap inits \o tails.

Definition some_m : Z ~> option Z := morph_of Some.

Definition mss : list Z ~> option Z :=
  maximum \o lmap sum \o segs \o lmap some_m.

Definition odot := horner_step maxplus.

Lemma horner_mss : maximum \o lmap sum \o inits =e foldr odot (Some 0).
Proof. apply (horner maxplus). Qed.

(* [tup] stays folded, and is inlined by extraction: it binds the recursive
   result once *)
Extraction Inline tup.
#[local] Hint Unfold odot horner_step maxplus max_monoid plus_monoid tup_step
  some_m : unfold_code.

Derive mss_linear in (mss =e morph_of mss_linear) as mss_calc.
Proof.
  unfold mss, segs.
  arewrite (map_promotion sum).
  arewrite (reduce_promotion max_monoid).
  arewrite (lmap_comp maximum (lmap sum)).
  arewrite (lmap_comp (maximum \o lmap sum) inits).
  rewrite horner_mss.
  arewrite (scan_lemma odot (Some 0)).
  arewrite (scan_tupling max_monoid odot (Some 0)).
  arewrite (foldr_lmap (tup_step max_monoid odot) some_m (Some 0, Some 0)).
  finished.
Qed.

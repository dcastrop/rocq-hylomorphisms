Set Warnings "-disj-pattern-notation,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Uint63.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Stdlib Require Import ZifyUint63.

Coercion is_true b := b = true.

Lemma eta_pair {A B} (p : A * B) : p = (fst p, snd p).
Proof. destruct p; trivial. Qed.

Lemma wf_lt : well_founded lt.
Proof.
  cut (forall x y, y < x -> Acc lt y).
  - intros H x. apply (H (S x) x); lia.
  - fix Ih 1.
    intros [|x] y LT; try lia.
    constructor. intros z LZ. apply (Ih x). lia.
Defined.

Lemma negb_lt_le x h : negb (x <? h)%uint63 -> (h <=? x)%uint63.
Proof. destruct (ltbP x h); [discriminate|]; intros; apply leb_spec; lia. Qed.

Lemma negb_lt_x_x x : negb (x <? x)%uint63.
Proof. destruct (ltbP x x); [lia | reflexivity]. Qed.

Lemma lt_le x h : (x <? h)%uint63 -> (x <=? h)%uint63.
Proof. destruct (ltbP x h); [|discriminate]; intros; apply leb_spec; lia. Qed.

Lemma leb_trans x h i
  : (x <=? h)%uint63 -> (h <=? i)%uint63 -> (x <=? i)%uint63.
Proof. intros E1%leb_spec E2%leb_spec; apply leb_spec; lia. Qed.

Lemma In_middle A l (x : A) r : In x (l ++ x :: r).
Proof. apply in_elt. Qed.

Definition All {A : Type} (P : A -> Prop) (l : list A) : Prop :=
  forall x, In x l -> P x.

(** [map] over the elements for which [f] gives a value *)
Fixpoint map_some {X Y} (f : X -> option Y) (l : list X) : list Y :=
  match l with
  | nil => nil
  | x :: l =>
      match f x with Some y => y :: map_some f l | None => map_some f l end
  end.

(** A [map] after a [filter] is a partial map *)
Lemma map_filter {X Y} (q : X -> bool) (f : X -> Y) l
  : map f (filter q l) = map_some (fun x => if q x then Some (f x) else None) l.
Proof.
  induction l as [|x l Ih]; cbn; [|destruct (q x); cbn; rewrite Ih];
    reflexivity.
Qed.

Lemma map_some_ext {X Y} (f g : X -> option Y) l
  : (forall x, f x = g x) -> map_some f l = map_some g l.
Proof.
  intros E; induction l as [|x l Ih]; cbn; [|rewrite E, Ih]; reflexivity.
Qed.

Lemma option_map_id {X} (o : option X) : option_map (fun x => x) o = o.
Proof. destruct o; reflexivity. Qed.

Lemma int_pred_lt (n : int) : (n =? 0)%uint63 = false ->
  Z.to_nat (Uint63.to_Z (n - 1)) < Z.to_nat (Uint63.to_Z n).
Proof. lia. Qed.

(* Case analysis on the tests in [if]s, innermost first, closing branches by
   [lia] *)
Ltac int_cases :=
  repeat match goal with
         | |- context [if ?c then _ else _] =>
             lazymatch c with
             | context [if _ then _ else _] => fail
             | _ => idtac
             end;
             destruct c eqn:?; cbv iota
         end;
  cbn [option_map];
  first [reflexivity | exfalso; lia | f_equal; lia | do 2 f_equal; lia].

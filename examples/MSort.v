Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

From Hylo Require Import Hylo.
Require Import Hylo.Utils.

Require Import Hylo.Examples.BTree.

From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Sint63.

Fixpoint mergeL l1 l2 {struct l1} :=
  let fix merge_aux l2 :=
    match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | cons a1 l1', cons a2 l2' =>
      if a1 <=? a2 then cons a1 (mergeL l1' l2) else cons a2 (merge_aux l2')
    end%sint63
  in merge_aux l2.

Definition merge : App (TreeF (list int) unit) (list int) ~> list int :=
  morph_of (fun x : App (TreeF (list int) unit) (list int) =>
    match a_out x with
    | node _ l r => mergeL l r
    | leaf e => e
    end).

Fixpoint splitL (x : list int) (accL accR : list int) :=
  match x with
  | nil => (accL, accR)
  | cons x xs => splitL xs accR (cons x accL)
  end.

Abbreviation max := Nat.max.

Definition len_pair (p : list int * list int) : nat
  := max (length (fst p)) (length (snd p)).

Lemma splitL_len : forall x a1 a2,
    length (fst (splitL x a1 a2)) <= max (length a1) (length a2) + length x /\
      length (snd (splitL x a1 a2)) <= max (length a1) (length a2) + length x.
Proof.
  induction x as [|h t Ih]; intros a1 a2; unfold len_pair; simpl in *.
  - lia.
  - specialize (Ih a2 (cons h a1)); simpl in *; lia.
Qed.

Definition c_split (x : list int) : App (TreeF (list int) unit) (list int) :=
  match x with
  | nil | cons _ nil => a_leaf x
  | _ => let (l, r) := splitL x nil nil in a_node tt l r
  end.
Arguments c_split x /.

Lemma split_fin : respects_relation c_split (@length int) lt.
Proof.
  intros [|h [|h' t]] p; simpl in *; try apply (dom_leaf _ p).
  revert p; rewrite (eta_pair (splitL _ _ _)); simpl; intros p.
  destruct (splitL_len t (h::nil) (h'::nil)) as [H1 H2]; simpl in *.
  destruct p as [[|] V]; rewrite PeanoNat.Nat.lt_succ_r; trivial.
Qed.

Definition tsplit : RCoalg (TreeF (list int) unit) (list int)
  := mk_wf_coalg wf_lt split_fin.

Definition msort : Ext (cata merge \o rana tsplit).
Proof.
  calculate; rewrite cata_ana_hylo.
  with_strategy opaque [wf_lt] simpl.
  reflexivity.
Defined.

Module Tests.
  Import List.
  Definition test := (1 :: 7 :: 2 :: 8 :: 10 :: 8 :: 1 :: nil)%sint63.
  Fixpoint cycle n :=
    match n with
    | 0 => test
    | S n => test ++ cycle n
    end.
  Definition largeTest := Eval compute in cycle 10.
  (* Uncomment to run the tests:
    Eval compute in msort largeTest.
  *)
End Tests.

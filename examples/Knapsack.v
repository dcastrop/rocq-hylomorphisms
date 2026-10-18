Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

From Hylo Require Import Hylo.
Require Import Hylo.Utils.

From Stdlib Require Import List.
From Stdlib Require Import Sint63.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import PArray.

Require Import Hylo.Examples.Dyna.

Fixpoint max_int acc (l : list int) :=
  match l with
  | h :: t =>
      if (acc <? h)%sint63 then max_int h t
      else max_int acc t
  | nil => acc
  end.

Definition jw (w : int) : nat := Nat.pred (Z.to_nat (Uint63.to_Z w)).

Fixpoint memo_knapsack table (wvs : list (int * int)) :=
  match wvs with
  | nil => nil
  | (w, v) :: t =>
      if (0 <? w)%uint63 then
        match lookupT (jw w) table with
        | Some u => (u + v)%sint63 :: memo_knapsack table t
        | None => memo_knapsack table t
        end
      else memo_knapsack table t
  end.

Lemma memo_knapsack_morph wvs :
  forall t1 t2, LFixR t1 t2 -> memo_knapsack t1 wvs = memo_knapsack t2 wvs.
Proof.
  intros t1 t2 Rt; induction wvs as [|[w v] wvs Ih]; simpl; trivial.
  rewrite (lookupT_morph (eq_refl (jw w)) Rt), Ih; reflexivity.
Qed.

Definition knapsack_alg (wvs : list (int * int))
  (x : App NatF (Table NatF int)) : int
  := match x with
     | MkCont sx kx =>
         match sx with
         | inl tt => fun kx => 0%sint63
         | inr tt =>
             fun kx =>
               let table := kx (MkElem (inr tt) valid_inr_tt) in
               max_int 0 (memo_knapsack table wvs)
         end kx
     end.
Lemma knapsack_alg_morph wvs
  : forall x y, x =e y -> knapsack_alg wvs x =e knapsack_alg wvs y.
Proof.
  intros [sx kx] [sy ky] [Es Ek]; simpl in *.
  destruct sx as [[]|[]], sy as [[]|[]]; try destruct Es; trivial.
  rewrite (memo_knapsack_morph wvs (Ek _ _ eq_refl)); reflexivity.
Qed.

Definition knapsackA (wvs : list (int * int))
  : App NatF (Table NatF int) ~> int
  := Eval unfold knapsack_alg in MkMorph (knapsack_alg_morph wvs).

Fixpoint memo_knapsack_l (table : list int) (wvs : list (int * int)) :=
  match wvs with
  | nil => nil
  | (w, v) :: t =>
      if (0 <? w)%uint63 then
        match nth_error table (jw w) with
        | Some u => (u + v)%sint63 :: memo_knapsack_l table t
        | None => memo_knapsack_l table t
        end
      else memo_knapsack_l table t
  end.

Definition knapsack_list_ (wvs : list (int * int)) (x : App NatF (list int)) : int :=
  match x with
  | MkCont (inl tt) _ => 0%sint63
  | MkCont (inr tt) k => max_int 0 (memo_knapsack_l (k (MkElem (inr tt) valid_inr_tt)) wvs)
  end.

Lemma knapsack_list_morph wvs
  : forall x y, x =e y -> knapsack_list_ wvs x =e knapsack_list_ wvs y.
Proof.
  intros [[[]|[]] kx] [[[]|[]] ky] [Es Ek]; simpl in Es; cbn [cont shape] in Ek; try contradiction;
    simpl; [reflexivity|].
  rewrite (leibniz (Ek _ (MkElem (inr tt) valid_inr_tt) eq_refl)); reflexivity.
Qed.

Definition knapsackL wvs : App NatF (list int) ~> int :=
  MkMorph (knapsack_list_morph wvs).

Lemma knapsack_list wvs : knapsackA wvs =e knapsackL wvs \o fmap to_list.
Proof.
  intros [[[]|[]] k]; simpl; trivial; f_equal.
  induction wvs as [|[w v] wvs Ih]; simpl; trivial.
  rewrite lookupT_to_list, Ih; reflexivity.
Qed.

Fixpoint memo_arr (t : array int) (c : int) (wvs : list (int * int)) :=
  match wvs with
  | nil => nil
  | (w, v) :: wvs =>
      if ((0 <? w)%uint63 && (w <=? c)%uint63)%bool then (t.[(c - w)%uint63] + v)%sint63 :: memo_arr t c wvs
      else memo_arr t c wvs
  end.

Definition knapsack_arr_ (wvs : list (int * int)) (x : App NatF (array int * int)) : int :=
  match x with
  | MkCont (inl tt) _ => 0%sint63
  | MkCont (inr tt) k =>
      let (t, c) := k (MkElem (inr tt) valid_inr_tt) in max_int 0 (memo_arr t c wvs)
  end.

Lemma knapsack_arr_morph wvs
  : forall x y, x =e y -> knapsack_arr_ wvs x =e knapsack_arr_ wvs y.
Proof.
  intros [[[]|[]] kx] [[[]|[]] ky] [Es Ek]; simpl in Es; cbn [cont shape] in Ek;
    try contradiction; simpl; [reflexivity|].
  rewrite (leibniz (Ek _ (MkElem (inr tt) valid_inr_tt) eq_refl)); reflexivity.
Qed.

Definition knapsackArr wvs : App NatF (array int * int) ~> int :=
  MkMorph (knapsack_arr_morph wvs).

Lemma jw_ltb w c : (0 <? w)%uint63 = true ->
  Nat.ltb (jw w) (Z.to_nat (Uint63.to_Z c)) = (w <=? c)%uint63.
Proof.
  intros Hw%Uint63.ltb_spec; change (Uint63.to_Z 0) with 0%Z in Hw; unfold jw.
  destruct (w <=? c)%uint63 eqn:E.
  - apply Uint63.leb_spec in E; apply Nat.ltb_lt; lia.
  - apply Nat.ltb_ge.
    assert (~ (Uint63.to_Z w <= Uint63.to_Z c)%Z)
      by (intros H'; apply Uint63.leb_spec in H'; congruence); lia.
Qed.

Lemma jw_ix w c : (0 <? w)%uint63 = true -> (w <=? c)%uint63 = true ->
  ix (Z.to_nat (Uint63.to_Z c) - 1 - jw w) = (c - w)%uint63.
Proof.
  intros Hw%Uint63.ltb_spec Hc%Uint63.leb_spec; change (Uint63.to_Z 0) with 0%Z in Hw.
  pose proof (Uint63.to_Z_bounded c); pose proof (Uint63.to_Z_bounded w).
  apply Uint63.to_Z_inj; rewrite ix_spec, Uint63.sub_spec, Z.mod_small; unfold jw; lia.
Qed.

Lemma knapsack_arr_eq wvs : knapsackArr wvs =e knapsackL wvs \o fmap tl.
Proof.
  intros [[[]|[]] k]; simpl; trivial.
  destruct (k _) as [t c]; simpl; f_equal.
  induction wvs as [|[w v] wvs Ih]; simpl; trivial.
  destruct (0 <? w)%uint63 eqn:Ew; simpl; [|exact Ih].
  rewrite nth_tl_arr, jw_ltb by exact Ew.
  destruct (w <=? c)%uint63 eqn:Ec; rewrite Ih; [rewrite jw_ix by trivial|]; reflexivity.
Qed.

Section Knapsack.
  Variable wvs : list (int * int).

  Derive knapsack in (dyna (knapsackA wvs) out_int_c =e knapsack) as knapsack_calc.
  Proof.
    unfold dyna.
    rewrite (headT_to_list 0%sint63).
    arewrite (table_to_list out_int_c (knapsack_list wvs)).
    rewrite hylo_out_int.
    finished.
  Qed.

  Derive knapsack_arr
    in (forall n, (Uint63.to_Z n < Uint63.to_Z max_length)%Z -> knapsack n = knapsack_arr n)
    as knapsack_arr_calc.
  Proof.
    intros n Hn; unfold knapsack; cbn [Morphism.app comp].
    refine (eq_trans (dyna_array 0%sint63 (knapsack_arr_eq wvs) Hn) _).
    subst knapsack_arr; reflexivity.
  Qed.
End Knapsack.

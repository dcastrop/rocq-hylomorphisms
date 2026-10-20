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
From Stdlib Require Import ZifyUint63.

Require Import Hylo.Dyna.
Require Import Hylo.Examples.ArrayTable.

(** * The specification: the naive (exponential) recursion
  *
  * [knapsack_naive n] is the best value of the items [(w, v)] that fit in [n],
  * one recursive call per item. The shapes are the items that fit, and the
  * positions their indices. *)
Fixpoint max_int acc (l : list int) :=
  match l with
  | h :: t =>
      if (acc <? h)%sint63 then max_int h t
      else max_int acc t
  | nil => acc
  end.

Definition fits (n : int) (wv : int * int) : bool :=
  ((0 <? Datatypes.fst wv)%uint63 && (Datatypes.fst wv <=? n)%uint63)%bool.

Lemma items_valid_morph
  : forall x y : list (int * int) * nat, x =e y ->
    Nat.ltb (Datatypes.snd x) (List.length (Datatypes.fst x))
    =e Nat.ltb (Datatypes.snd y) (List.length (Datatypes.fst y)).
Proof. intros x y E; apply leibniz in E; subst y; reflexivity. Qed.

#[export] Instance ItemsF : Cont (list (int * int)) nat :=
  { valid := MkMorph items_valid_morph }.

(* The children and the values of their items *)
Fixpoint kids {X} (s : list (int * int))
  : (forall i, Nat.ltb i (List.length s) = true -> X) -> list (X * int) :=
  match s with
  | nil => fun _ => nil
  | (w, v) :: s' =>
      fun k => (k 0 eq_refl, v) :: @kids X s' (fun i H => k (S i) H)
  end.
Arguments kids {X} s k.

Lemma kids_ext {X} s (k1 k2 : forall i, Nat.ltb i (List.length s) = true -> X)
  : (forall i H, k1 i H = k2 i H) -> kids s k1 = kids s k2.
Proof.
  revert k1 k2; induction s as [|[w v] s Ih]; intros k1 k2 Hk; cbn; trivial.
  rewrite Hk; f_equal; apply Ih; intros; apply Hk.
Qed.

Definition naive_alg_ (x : App ItemsF int) : int :=
  max_int 0 (map (fun rv => (Datatypes.fst rv + Datatypes.snd rv)%sint63)
                 (kids (shape x) (fun i H => cont x (MkElem i H)))).

Lemma naive_alg_morph : forall x y, x =e y -> naive_alg_ x =e naive_alg_ y.
Proof.
  intros [s1 k1] [s2 k2] [Es Ek]; apply leibniz in Es; cbn in Es; subst s2.
  unfold naive_alg_; cbn; do 2 f_equal; apply kids_ext; intros; apply Ek; auto.
Qed.

Definition naive_alg : Alg ItemsF int := MkMorph naive_alg_morph.

Definition naive_c_ wvs (n : int) : App ItemsF int :=
  let s := filter (fits n) wvs in
  MkCont s (fun e => (n - Datatypes.fst (nth (val e) s (0, 0)%uint63))%uint63).

Lemma naive_c_morph wvs
  : forall x y, x =e y -> naive_c_ wvs x =e naive_c_ wvs y.
Proof. intros x y E; apply leibniz in E; subst y; reflexivity. Qed.

Lemma naive_c_fin wvs
  : respects_relation (MkMorph (naive_c_morph wvs))
      (fun n => Z.to_nat (Uint63.to_Z n)) lt.
Proof.
  intros n [i V]; pose proof V as L.
  change (Nat.ltb i (length (filter (fits n) wvs)) = true) in L.
  apply (proj1 (Nat.ltb_lt _ _)), (nth_In _ (0, 0)%uint63), filter_In in L.
  cbn -[Uint63.to_Z nth filter]; destruct (nth i _ _) as [w v], L as [_ Hf].
  unfold fits in Hf; cbn [Datatypes.fst] in *; lia.
Qed.

Definition naive_c wvs : RCoalg ItemsF int :=
  mk_wf_coalg wf_lt (naive_c_fin (wvs := wvs)).

Definition knapsack_naive wvs : int ~> int := hylo naive_alg (naive_c wvs).

(** * The calculation
  *
  * [naive_fmap] unfolds the naive algebra on the naive coalgebra; the rest
  * is [reenumerate] (with [look_down]) and [dyna_memo] from [Dyna]. *)
Lemma kids_nth {X} (g : int * int -> X) s d
  : kids s (fun i _ => g (nth i s d)) = map (fun p => (g p, Datatypes.snd p)) s.
Proof. induction s as [|[w v] s Ih]; cbn; [|f_equal]; trivial. Qed.

Lemma naive_fmap wvs (g : int ~> int) b
  : naive_alg (fmap g (naive_c wvs b))
    = max_int 0 (map (fun rv => (Datatypes.fst rv + Datatypes.snd rv)%sint63)
        (map (fun p => (g (b - Datatypes.fst p)%uint63, Datatypes.snd p))
           (filter (fits b) wvs))).
Proof.
  cbn -[filter max_int]; unfold naive_alg_; cbn -[filter max_int].
  rewrite (kids_nth (fun p => g (b - Datatypes.fst p)%uint63)); reflexivity.
Qed.

Section Calculation.
  Variable wvs : list (int * int).

  (** Step 1: the algebra that reads the subproblems through a [look] down the
    * count-down: an item fits iff its subproblem is there *)
  Derive knap_alg_ in
    (forall (g : int ~> int) b,
        naive_alg (fmap g (naive_c wvs b))
        = knap_alg_ (look_rec (Pa := int) out_int_c g b))
    as knap_look.
  Proof.
    intros g b; rewrite naive_fmap, map_filter_pair; unfold fits.
    erewrite map_some_ext by (intros; rewrite <- look_down; reflexivity).
    abstracted.
  Qed.

  Lemma knap_alg_eq : forall l1 l2, l1 =e l2 -> knap_alg_ l1 =e knap_alg_ l2.
  Proof.
    intros l1 l2 E; apply eq_leibniz; unfold knap_alg_; do 2 f_equal.
    apply map_some_ext; intros p; rewrite (leibniz (E _)); reflexivity.
  Qed.

  Definition knap_alg := MkMorph knap_alg_eq.

  (** Step 2: the program, a dynamorphism on persistent arrays *)
  Derive knapsack_arr in (knapsack_naive wvs =e knapsack_arr)
    as knapsack_arr_calc.
  Proof.
    unfold knapsack_naive.
    rewrite (reenumerate (U := ATab int) (alg := knap_alg) knap_look).
    rewrite dyna_memo.
    finished.
  Qed.
End Calculation.

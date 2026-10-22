Set Warnings "-bad-template-constraint,-disj-pattern-notation".
Set Warnings "-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Hylo.
Require Import Hylo.Lists.

From Stdlib Require Import List.
From Stdlib Require Import Sint63.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import ZifyUint63.
From Stdlib Require Import ZifySint63.

Require Import Hylo.Extraction.Specialise.

(** * The specification: the naive (exponential) recursion
  *
  * [knapsack_naive n] is the best value of the items [(w, v)] that fit in [n],
  * one recursive call per item. The shapes are the items that fit, and the
  * positions their indices. *)
Definition imax (a b : int) : int := if (a <? b)%sint63 then b else a.

(* The signed maximum, a monoid with unit [min_int] *)
Program Definition max_m : Monoid int :=
  {| skip := Sint63.min_int; par := morph_of (fun a => morph_of (imax a)) |}.
Solve All Obligations with
  intros; cbn; unfold imax; int_cases.

Definition value : int * int ~> int :=
  morph_of (fun rv => (Datatypes.fst rv + Datatypes.snd rv)%sint63).

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
  imax 0 (reduce max_m value (kids (shape x) (fun i H => cont x (MkElem i H)))).

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
Arguments naive_c_fin : clear implicits.

Definition naive_c wvs : RCoalg ItemsF int :=
  mk_wf_coalg wf_lt (naive_c_fin wvs).

Definition knapsack_naive wvs : int ~> int := hylo naive_alg (naive_c wvs).

(** * The calculation
  *
  * The subproblems are read from a table ([reenumerate]), looked up down the
  * count-down ([look_down]) with random access ([fast_drop_walk]), and the
  * table is built by a loop ([dyna_loop]). *)
Local Abbreviation wt p := (Datatypes.fst p).
Local Abbreviation vl p := (Datatypes.snd p).

Lemma kids_nth {X} (g : int * int -> X) s d
  : kids s (fun i _ => g (nth i s d)) = map (fun p => (g p, vl p)) s.
Proof. induction s as [|[w v] s Ih]; cbn; [|f_equal]; trivial. Qed.

(* The naive step: the best value over the items that fit *)
Lemma naive_step wvs (g : int ~> int) b
  : naive_alg (fmap g (naive_c wvs b))
    = imax 0 (reduce max_m value (map_some (fun p =>
        if fits b p then Some (g (b - wt p)%uint63, vl p) else None) wvs)).
Proof.
  cbn -[filter reduce imax]; unfold naive_alg_; cbn -[filter reduce imax].
  rewrite (kids_nth (fun p => g (b - wt p)%uint63)), map_filter; reflexivity.
Qed.

(* An item fits iff its subproblem is in the table, down the count-down *)
Lemma fits_look (g : int ~> int) b p
  : (if fits b p then Some (g (b - wt p)%uint63, vl p) else None)
    = option_map (fun r => (r, vl p)) (look_rec out_int_c g b (wt p)).
Proof. unfold fits; rewrite look_down; destruct (_ && _)%bool; reflexivity.
Qed.

Section Calculation.
  Variable wvs : list (int * int).

  (** Step 1: the algebra that reads the subproblems from the table *)
  Derive knap_alg_ in
    (forall (g : int ~> int) b,
        naive_alg (fmap g (naive_c wvs b))
        = knap_alg_ (look_rec out_int_c g b))
    as knap_look.
  Proof.
    intros g b.
    rewrite naive_step.
    setoid_rewrite fits_look.
    rewrite reduce_map_option.
    abstracted.
  Qed.

  Lemma knap_alg_eq : forall l1 l2, l1 =e l2 -> knap_alg_ l1 =e knap_alg_ l2.
  Proof.
    intros l1 l2 E; apply eq_leibniz; unfold knap_alg_; f_equal.
    apply reduce_ext; intros [w v]; cbn; rewrite (leibniz (E w)); reflexivity.
  Qed.

  Definition knap_alg := MkMorph knap_alg_eq.
  #[local] Hint Unfold knap_alg knap_alg_ max_m value : unfold_code.

  (** Step 2: the loop's step, from the table, and its first entry *)
  Derive knap_step in (knap_alg \o look_with fast_drop_walk \o nat_next
                       =e knap_step) as knap_step_calc.
  Proof. finished. Qed.

  (* With an empty table no item fits *)
  Lemma knap_base : knap_alg (look_with fast_drop_walk nat_leaf) =e 0%uint63.
  Proof.
    cbn [knap_alg app]; unfold knap_alg_; cbn -[reduce imax].
    match goal with |- context [reduce ?m ?f] =>
      assert (E : forall l, reduce m f l = min_int) end.
    { induction l as [|h t Ih]; [apply leibniz, reduce_nil|].
      rewrite (leibniz (reduce_cons _ _ _ _)), Ih; reflexivity. }
    rewrite E; reflexivity.
  Qed.

  (** Step 3: the program, a loop over a persistent array *)
  Derive knapsack_arr in (knapsack_naive wvs =e morph_of knapsack_arr)
    as knapsack_arr_calc.
  Proof.
    unfold knapsack_naive.
    (* Memoise: the subproblems are read from a table *)
    erewrite reenumerate.
    (* The table of a count-down is built by a loop *)
    erewrite dyna_loop.
    (* The loop's step, its first entry, and the algebra on the table *)
    2: exact knap_step_calc.
    2: exact knap_base.
    2: exact knap_look.
    finished.
  Qed.
End Calculation.

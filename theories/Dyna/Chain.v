Set Warnings "-bad-template-constraint,-disj-pattern-notation".
Set Warnings "-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Core.
Require Import Hylo.Schemes.
Require Import Hylo.Dyna.Memo.
Require Import Hylo.Dyna.Dynamorphism.

From Stdlib Require Import Uint63.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import ZifyUint63.

(** * Chains
  *
  * A dynamorphism goes through a list of inputs, the chain of a coalgebra
  * [e : RCoalg NatF B]. Its table holds their results, and the results it
  * needs are looked up by their distance [j] down the chain. *)
Definition NatF := LoopF unit.

(** The next input of a chain, if any *)
Definition nat_child `{setoid X} (x : App NatF X) : option X :=
  match x with
  | MkCont (inl tt) _ => None
  | MkCont (inr tt) k => Some (k (MkElem (inr tt) (loop_step_valid unit)))
  end.

Lemma nat_child_hom `{setoid X} `{setoid Y} (h : X ~> Y) a b
  : a =e fmap h b -> nat_child a =e option_map h (nat_child b).
Proof.
  destruct a as [[[]|[]] ka], b as [[[]|[]] kb]; intros [Es Ek]; cbn in Es;
    try contradiction; cbn; [exact I | apply Ek; reflexivity].
Qed.

(** Counting down on machine integers *)
Definition out_int (n : int) : App NatF int :=
  MkCont (if (n =? 0)%uint63 then inl tt else inr tt) (fun _ => (n - 1)%uint63).

Lemma out_int_fin
  : respects_relation out_int (fun n => Z.to_nat (Uint63.to_Z n)) lt.
Proof.
  intros n p; simpl in *; revert p; unfold out_int.
  destruct (n =? 0)%uint63 eqn:E; intros p; simpl in *.
  - destruct (loop_done_empty p).
  - apply int_pred_lt, E.
Qed.

Definition out_int_c : RCoalg NatF int := mk_wf_coalg wf_lt out_int_fin.

(** * Walks down a chain
  *
  * [iwalk step j x] takes [j] steps from [x] by recursion on [out_int_c]. *)
Section IntPaths.
  Context `{setoid X} (step : X ~> App NatF X).

  Definition iwalk_alg_ (x : App NatF (X -> option X)) (y : X) : option X :=
    match x with
    | MkCont (inl tt) _ => Some y
    | MkCont (inr tt) k =>
        match nat_child (step y) with
        | Some z => k (MkElem (inr tt) (loop_step_valid unit)) z
        | None => None
        end
    end.

  Lemma iwalk_alg_eq : forall x y, x =e y -> iwalk_alg_ x =e iwalk_alg_ y.
  Proof.
    intros [[[]|[]] kx] [[[]|[]] ky] [Es Ek] y; cbn in Es; try contradiction;
      cbn; [apply e_refl|].
    destruct (nat_child (step y)); [apply Ek; reflexivity | exact I].
  Qed.

  Definition iwalk : int ~> (X -> option X) :=
    hylo (MkMorph iwalk_alg_eq) out_int_c.

  Lemma iwalk_unfold j x : iwalk j x =e iwalk_alg_ (fmap iwalk (out_int j)) x.
  Proof. exact (hylo_unr (MkMorph iwalk_alg_eq) out_int_c j x). Qed.

  (* [x] is the first step *)
  Definition iwalk_child (j : int) (x : X) : option X :=
    if (j =? 0)%uint63 then None else iwalk (j - 1)%uint63 x.

  Definition iwalk_from (y : App NatF X) (j : int) : option X :=
    match nat_child y with Some x => iwalk_child j x | None => None end.
End IntPaths.

(** A map between steps that commutes with one step commutes with walks *)
Lemma iwalk_hom `{setoid X} `{setoid Y}
  (sx : X ~> App NatF X) (sy : Y ~> App NatF Y) (h : X ~> Y)
  (Hh : forall x y, y =e h x -> sy y =e fmap h (sx x))
  : forall j x y, y =e h x -> iwalk sy j y =e option_map h (iwalk sx j x).
Proof.
  intros j; remember (Z.to_nat (Uint63.to_Z j)) as n eqn:En; revert j En.
  induction n as [|n Ih]; intros j En x y E;
    rewrite (iwalk_unfold sy j y), (iwalk_unfold sx j x);
    unfold out_int; destruct (j =? 0)%uint63 eqn:Ej; cbn -[iwalk];
    [exact E | exfalso; lia | exact E |].
  pose proof (nat_child_hom (Hh x y E)) as Hp.
  destruct (nat_child (sx x)), (nat_child (sy y)); cbn -[iwalk] in Hp |- *;
    try contradiction; [apply Ih; [lia | exact Hp] | exact I].
Qed.

Lemma iwalk_from_hom `{setoid X} `{setoid Y}
  (sx : X ~> App NatF X) (sy : Y ~> App NatF Y) (h : X ~> Y)
  (Hh : forall x y, y =e h x -> sy y =e fmap h (sx x)) y y'
  : y' =e fmap h y ->
    forall j, iwalk_from sy y' j =e option_map h (iwalk_from sx y j).
Proof.
  intros Hy j; unfold iwalk_from, iwalk_child.
  pose proof (nat_child_hom Hy) as Hp.
  destruct (nat_child y), (nat_child y'), (j =? 0)%uint63;
    cbn -[iwalk] in Hp |- *; try contradiction; try exact I;
    apply iwalk_hom; assumption.
Qed.

(** * Changing the coalgebra
  *
  * [alg] reads the results it needs through a [look] at distances down the
  * chain of [e]. [look_rec] recomputes them, [look_tbl] reads them from the
  * table. *)
Section Reenumerate.
  Context `{setoid A} `{setoid B} `{eU : setoid U} `{!Initial (Memo NatF A) U}
    (w : int -> U -> option U)
    (Hw : forall j t, w j t =e iwalk_child (mtail \o l_out) j t).

  Definition look_rec (e : RCoalg NatF B) (g : B -> A) (b : B) (j : int)
    : option A :=
    option_map g (iwalk_from e (e b) j).

  Definition look_with_ (x : App NatF U) (j : int) : option A :=
    option_map (mhead \o l_out)
      (match nat_child x with Some t => w j t | None => None end).

  Lemma look_with_walk x j
    : look_with_ x j
      =e option_map (mhead \o l_out) (iwalk_from (mtail \o l_out) x j).
  Proof.
    unfold look_with_, iwalk_from.
    destruct (nat_child x); [apply option_map_eq, Hw | exact I].
  Qed.

  Lemma look_with_eq : forall x y, x =e y -> look_with_ x =e look_with_ y.
  Proof.
    intros x y E j; rewrite !look_with_walk; apply option_map_eq; symmetry.
    rewrite <- (option_map_id (iwalk_from _ x j)).
    apply (iwalk_from_hom (h := id)).
    - intros a b Eab; rewrite Eab; symmetry; apply fmap_id.
    - rewrite E; symmetry; apply fmap_id.
  Qed.

  Definition look_with : App NatF U ~> (int -> option A) :=
    MkMorph look_with_eq.

  (** The invariant: looking into the table is recomputing *)
  Lemma look_table (e : RCoalg NatF B) (g : B ~> A) b
    : look_with (fmap (table e g) (e b)) =e look_rec e g b.
  Proof.
    intros j; cbn [look_with app]; rewrite look_with_walk; etransitivity.
    - apply option_map_eq, (iwalk_from_hom (h := table e g) (sx := e));
        [intros x y E; rewrite E; apply table_step | reflexivity].
    - unfold look_rec; destruct (iwalk_from e (e b) j);
        [exact (mhead_table e g _) | exact I].
  Qed.

  Theorem reenumerate `{F : Cont Sf Pf} (an : App F A ~> A) (cn : RCoalg F B)
    (e : RCoalg NatF B) (alg : (int -> option A) ~> A)
    (Hlook : forall (g : B ~> A) b,
        an (fmap g (cn b)) =e alg (look_rec e g b))
    : hylo an cn =e dyna (alg \o look_with) e.
  Proof.
    unfold dyna; rewrite <- (hylo_uniq_r (f := table e (hylo an cn))).
    - symmetry; apply mhead_table.
    - rewrite table_unfold at 1; intros b; cbn [app comp].
      apply (app_eq l_in), (app_eq mcons); split; [|reflexivity].
      rewrite (hylo_unr an cn b); etransitivity; [apply (Hlook _ b)|].
      apply (app_eq alg); symmetry; apply look_table.
  Qed.
End Reenumerate.
Arguments reenumerate {A H B H0 U eU Initial0} [w] Hw {Sf Esh Pf F} [an cn e]
  alg Hlook x.

(** * Tables of count-downs are built by loops, counting up *)
Section NatLayers.
  Context `{setoid X}.

  Definition nat_leaf : App NatF X :=
    MkCont (inl tt) (fun e => False_rect _ (loop_done_empty e)).

  Lemma nat_next_eq : forall x y : X, x =e y ->
    MkCont (F := NatF) (inr tt) (fun _ => x) =e MkCont (inr tt) (fun _ => y).
  Proof. intros x y E; split; [reflexivity | intros; exact E]. Qed.

  (* The layer whose only child is [x] *)
  Definition nat_next : X ~> App NatF X := MkMorph nat_next_eq.
End NatLayers.

Section NatLoop.
  Context `{setoid A} `{eT : setoid T} `{!Initial (Memo NatF A) T}.

  (* The table for [i + 1] from the table for [i], given the new entry [st] *)
  Definition memo_step (st : T ~> A) : T ~> T :=
    l_in \o mcons \o pair st nat_next.

  Definition memo_base (b : A) : T := l_in (mcons (b, nat_leaf)).

  Context (a : App NatF T ~> A) (st : T ~> A) (b : A)
    (Hst : a \o nat_next =e st) (Hb : a nat_leaf =e b).

  (* The algebra of [dyna a] *)
  #[local] Abbreviation alg := (l_in \o mcons \o pair a id).

  Lemma memo_succ i : ((i + 1) =? 0)%uint63 = false ->
    hylo alg out_int_c (i + 1)%uint63 =e memo_step st (hylo alg out_int_c i).
  Proof.
    intros Hi; rewrite (hylo_unr _ _ (i + 1)%uint63).
    assert (E : fmap (hylo alg out_int_c) (out_int_c (i + 1)%uint63)
                =e nat_next (hylo alg out_int_c i)).
    { split; cbn -[hylo]; [rewrite Hi; reflexivity|].
      intros; replace (i + 1 - 1)%uint63 with i by lia; reflexivity. }
    apply (app_eq l_in), (app_eq mcons); split; [|exact E].
    etransitivity; [apply (app_eq a), E | apply Hst].
  Qed.

  Lemma memo_zero : hylo alg out_int_c 0%uint63 =e memo_base b.
  Proof.
    assert (E : fmap (hylo alg out_int_c) (out_int_c 0%uint63) =e nat_leaf)
      by (split; [reflexivity | intros e; destruct (loop_done_empty e)]).
    rewrite hylo_unr; apply (app_eq l_in), (app_eq mcons); split; [|exact E].
    etransitivity; [apply (app_eq a), E | apply Hb].
  Qed.

  Lemma memo_loop n
    : hylo alg out_int_c n
      =e loop n (fun _ => memo_step st) (0%uint63, memo_base b).
  Proof.
    enough (Hl : forall m i, Z.to_nat (Uint63.to_Z n - Uint63.to_Z i) = m ->
              (i <=? n)%uint63 = true ->
              loop n (fun _ => memo_step st) (i, hylo alg out_int_c i)
              =e hylo alg out_int_c n).
    { rewrite <- (Hl _ 0%uint63 eq_refl) by lia.
      apply app_eq; split; [reflexivity | apply memo_zero]. }
    induction m as [|m Ih]; intros i Em Hi; rewrite loop_unfold;
      destruct (i <? n)%uint63 eqn:E; try (exfalso; lia);
      [replace i with n by lia; reflexivity|].
    rewrite <- (Ih (i + 1)%uint63) by lia.
    apply app_eq; split; [reflexivity | symmetry; apply memo_succ; lia].
  Qed.

  Lemma dyna_loop
    : dyna a out_int_c
      =e mhead \o l_out
           \o morph_of (fun n =>
                 loop n (fun _ => memo_step st) (0%uint63, memo_base b)).
  Proof.
    intros n; unfold dyna; cbn [app comp].
    apply (app_eq mhead), (app_eq (coalg (l_out (T := T)))), memo_loop.
  Qed.
End NatLoop.

(** * Looking down a count-down *)
Lemma iwalk_down : forall j b,
  iwalk out_int_c j b = if (j <=? b)%uint63 then Some (b - j)%uint63 else None.
Proof.
  intros j; remember (Z.to_nat (Uint63.to_Z j)) as n eqn:En; revert j En.
  induction n as [|n Ih]; intros j En b;
    rewrite (leibniz (iwalk_unfold _ j b)); unfold out_int;
    destruct (j =? 0)%uint63 eqn:Ej; cbn -[iwalk];
    destruct (b =? 0)%uint63 eqn:Eb; cbn -[iwalk];
    try rewrite (Ih (j - 1)%uint63) by lia; int_cases.
Qed.

(** Looking [j] down the count-down from [b] recomputes [b - j] *)
Lemma look_down `{setoid A} (g : int -> A) b j
  : look_rec out_int_c g b j
    = if ((0 <? j)%uint63 && (j <=? b)%uint63)%bool then Some (g (b - j)%uint63)
      else None.
Proof.
  unfold look_rec, iwalk_from, iwalk_child.
  destruct (j =? 0)%uint63 eqn:Ej; cbn -[iwalk];
    destruct (b =? 0)%uint63 eqn:Eb; cbn -[iwalk]; try rewrite iwalk_down;
    int_cases.
Qed.

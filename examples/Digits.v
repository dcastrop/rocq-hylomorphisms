Set Warnings "-disj-pattern-notation,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import Hylo.Hylo.
Require Import Hylo.Lists.
Require Import Hylo.Extraction.Specialise.


From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Uint63.

Open Scope uint63_scope.

Definition digits_ (b n : int) : App (ListF int) int :=
  MkCont (if n =? 0 then s_nil else s_cons (n mod b)) (fun _ => n / b).

Lemma digits_fin b (Hb : (1 <? b) = true)
  : respects_relation (digits_ b) (fun n => Z.to_nat (to_Z n)) lt.
Proof.
  intros n p; simpl in *; revert p; unfold digits_.
  destruct (n =? 0) eqn:E; intros p; simpl in *.
  - destruct (dom_nil_false p).
  - apply ltb_spec in Hb; apply eqb_false_spec in E; rewrite div_spec.
    assert (Hn : (0 < to_Z n)%Z).
    { pose proof (to_Z_bounded n).
      assert (to_Z n <> 0)%Z by (intros H'; apply E, to_Z_inj; exact H'); lia. }
    pose proof (Z.div_lt _ _ Hn Hb); lia.
Qed.

Definition digits b (Hb : (1 <? b) = true) : RCoalg (ListF int) int :=
  mk_wf_coalg wf_lt (digits_fin Hb).
Arguments digits : clear implicits.

Lemma cons_valid (d : int) : valid (F := ListF int) (s_cons d, tt).
Proof. reflexivity. Qed.

Definition sq (x : int) : int := x * x.
Arguments sq : simpl never.

Definition digit_pow (x d : int) : int := if d =? 0 then 1 else x.

Definition pow_alg (x : int) : App (ListF int) int ~> int :=
  morph_of (fun a : App (ListF int) int =>
    match a with
    | MkCont s k =>
        match s as s return (Container.Pos (ListF int) s -> _) -> _ with
        | s_nil => fun _ => 1
        | s_cons d => fun k => digit_pow x d * sq (k (MkElem tt (cons_valid d)))
        end k
    end).

Definition sum_alg : App (ListF int) int ~> int :=
  morph_of (fun a : App (ListF int) int =>
    match a with
    | MkCont s k =>
        match s as s return (Container.Pos (ListF int) s -> _) -> _ with
        | s_nil => fun _ => 0
        | s_cons d => fun k => d + k (MkElem tt (cons_valid d))
        end k
    end).

Lemma ilist_out_in {A} : ilist_coalg \o @ilist_alg A =e id.
Proof.
  intros [[|h] k]; simpl; constructor; simpl; auto with ffix;
    intros [[] V1] [[] V2] _; try discriminate.
  rewrite (bool_irrelevance V2 (p_cons eq_refl)); reflexivity.
Qed.

Definition power (x : int) : int ~> int :=
  cata (pow_alg x) \o rana (digits 2 eq_refl).

Definition sumsq : int ~> int :=
  cata sum_alg \o Lmap sq \o rana (digits 10 eq_refl).

#[local] Hint Unfold digits digits_ pow_alg sum_alg : unfold_code.

Section FastPower.
  Variable x : int.

  Derive fast_power in (power x =e morph_of fast_power) as fast_power_calc.
  Proof.
    unfold power.
    rewrite cata_ana_hylo.
    finished.
  Qed.
End FastPower.

Derive sumsq_fold in (sumsq =e morph_of sumsq_fold) as sumsq_fold_calc.
Proof.
  unfold sumsq, Lmap, everywhere, List.
  rewrite hylo_cata, hylo_map_fusion.
  rewrite hylo_ana, deforest by apply l_out_in.
  finished.
Qed.

Derive sumsq_unfold in (sumsq =e morph_of sumsq_unfold)
  as sumsq_unfold_calc.
Proof.
  unfold sumsq, Lmap, everywhere, List.
  rewrite hylo_cata, hylo_map_fusion.
  rewrite hylo_ana, deforest by apply l_out_in.
  rewrite hylo_map_shift.
  rewrite <- (deforest ilist_out_in).
  finished.
Qed.

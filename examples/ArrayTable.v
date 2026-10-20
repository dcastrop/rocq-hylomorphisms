Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

From Hylo Require Import Hylo.
Require Import Hylo.Utils.
Require Import Hylo.Dyna.

From Stdlib Require Import List.
From Stdlib Require Import Uint63.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import PArray.

(** * Memo tables for [NatF] as persistent arrays
  *
  * [ATab A] is an initial algebra of [Memo NatF] ([ATab_initial]), so it can
  * replace any other memo table in [dyna] ([dyna_iso]). *)
Section NatTables.
  Context `{Leibniz A}.

Definition ix (n : nat) : int := Uint63.of_Z (Z.of_nat n).

Lemma ix_spec n : (Z.of_nat n < wB)%Z -> Uint63.to_Z (ix n) = Z.of_nat n.
Proof. intros Hn; unfold ix; rewrite Uint63.of_Z_spec, Z.mod_small; lia. Qed.

Lemma ix_to_nat (n : int) : ix (Z.to_nat (Uint63.to_Z n)) = n.
Proof.
  unfold ix; rewrite Z2Nat.id by (apply Uint63.to_Z_bounded); apply Uint63.of_to_Z.
Qed.

Lemma to_nat_pred (n : int) : (n =? 0)%uint63 = false ->
  Z.to_nat (Uint63.to_Z n) = S (Z.to_nat (Uint63.to_Z (n - 1))).
Proof. intros E; pose proof (int_pred_lt E); pose proof (Uint63.to_Z_bounded n).
  rewrite Uint63.sub_spec in *; change (Uint63.to_Z 1) with 1%Z in *.
  rewrite Z.mod_small in * by lia; lia.
Qed.

(* Memo tables as arrays: the entries of [blk] at [top], ..., [0] (newest
   first), followed by [prev]. New blocks have [max_length] entries, filled
   with the first value written. *)
#[warnings="-register-all"]
Inductive ATab := MkATab { blk : array A; top : int; prev : option ATab }.

Fixpoint blk_list (b : array A) (k : nat) : list A :=
  b.[ix k] :: match k with 0 => nil | S k' => blk_list b k' end.

Fixpoint to_list (t : ATab) : list A :=
  match t with
  | MkATab b i p =>
      blk_list b (Z.to_nat (Uint63.to_Z i))
        ++ match p with Some q => to_list q | None => nil end
  end.

#[export] Instance ATab_eq : setoid ATab :=
  {| eqRel t1 t2 := to_list t1 = to_list t2;
     e_refl t := eq_refl;
     e_sym t1 t2 := @eq_sym _ _ _;
     e_trans t1 t2 t3 := @eq_trans _ _ _ _
  |}.
#[export] Instance ATab_no_def_eq : NoDefEq ATab := {}.

Definition single (v : A) : ATab := MkATab (make max_length v) 0 None.

(* [i <? length b] rules out the overflow of [i + 1] *)
Definition push (v : A) (t : ATab) : ATab :=
  match t with
  | MkATab b i p =>
      if ((i <? length b)%uint63 && (i + 1 <? length b)%uint63)%bool then MkATab b.[i + 1 <- v] (i + 1) p
      else MkATab (make max_length v) 0 (Some t)
  end.

Definition head (t : ATab) : A := (blk t).[top t].

Definition is_last (t : ATab) : bool :=
  ((top t =? 0)%uint63 && match prev t with None => true | Some _ => false end)%bool.

Definition rest (t : ATab) : ATab :=
  match t with
  | MkATab b i p =>
      if (i =? 0)%uint63 then match p with Some q => q | None => t end
      else MkATab b (i - 1) p
  end.

Lemma to_list_out t
  : to_list t = head t :: if is_last t then nil else to_list (rest t).
Proof.
  destruct t as [b i p]; unfold head, is_last, rest; cbn [blk top prev].
  destruct (i =? 0)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E; subst i; destruct p; reflexivity.
  - cbn [to_list]; rewrite (to_nat_pred E); cbn [blk_list app].
    rewrite <- (to_nat_pred E), ix_to_nat; reflexivity.
Qed.

Lemma blk_list_set b c v k
  : k < c -> (Z.of_nat c < wB)%Z -> blk_list b.[ix c <- v] k = blk_list b k.
Proof.
  intros Hk Hc; induction k as [|k Ih]; cbn [blk_list]; [|rewrite Ih by lia];
    rewrite get_set_other; trivial;
    intros E; apply (Logic.f_equal Uint63.to_Z) in E; rewrite !ix_spec in E by lia; lia.
Qed.

Lemma to_list_single v : to_list (single v) = v :: nil.
Proof.
  unfold single; cbn [to_list]; change (Z.to_nat (Uint63.to_Z 0)) with 0.
  cbn [blk_list app]; rewrite get_make; reflexivity.
Qed.

Lemma to_list_push v t : to_list (push v t) = v :: to_list t.
Proof.
  destruct t as [b i p]; unfold push.
  destruct ((i <? length b)%uint63 && (i + 1 <? length b)%uint63)%bool eqn:E.
  - apply andb_prop in E as [E1 E2]; apply Uint63.ltb_spec in E1, E2.
    pose proof (Uint63.to_Z_bounded i); pose proof (Uint63.to_Z_bounded (length b)).
    assert (Hs : Uint63.to_Z (i + 1) = (Uint63.to_Z i + 1)%Z).
    { rewrite Uint63.add_spec; change (Uint63.to_Z 1) with 1%Z; apply Z.mod_small; lia. }
    cbn [to_list]; replace (Z.to_nat (Uint63.to_Z (i + 1))) with (S (Z.to_nat (Uint63.to_Z i)))
      by lia.
    cbn [blk_list app].
    assert (Ei : ix (S (Z.to_nat (Uint63.to_Z i))) = (i + 1)%uint63).
    { apply Uint63.to_Z_inj; rewrite ix_spec, Hs; lia. }
    rewrite Ei, get_set_same by (apply Uint63.ltb_spec; lia).
    rewrite <- Ei, blk_list_set by lia; reflexivity.
  - cbn [to_list]; change (Z.to_nat (Uint63.to_Z 0)) with 0.
    cbn [blk_list app]; rewrite get_make; reflexivity.
Qed.

Lemma to_list_cons t : exists v l, to_list t = v :: l.
Proof. rewrite to_list_out; eauto. Qed.

Lemma head_list (x : A) t : head t = hd x (to_list t).
Proof. rewrite to_list_out; reflexivity. Qed.

Lemma is_last_list t : is_last t = match to_list t with _ :: nil => true | _ => false end.
Proof.
  rewrite to_list_out; destruct (is_last t); [reflexivity|].
  destruct (to_list_cons (rest t)) as [v [l E]]; rewrite E; reflexivity.
Qed.

Lemma rest_list t : is_last t = false -> to_list (rest t) = tl (to_list t).
Proof. intros L; rewrite (to_list_out t), L; reflexivity. Qed.

Definition atab_out_ (t : ATab) : App (Memo NatF A) ATab :=
  MkCont (head t, if is_last t then inl tt else inr tt) (fun _ => rest t).

Lemma atab_out_morph : forall t1 t2, t1 =e t2 -> atab_out_ t1 =e atab_out_ t2.
Proof.
  intros t1 t2 E; change (to_list t1 = to_list t2) in E.
  assert (Eh : head t1 = head t2)
    by (rewrite (head_list (head t1) t1), (head_list (head t1) t2), E; reflexivity).
  assert (El : is_last t1 = is_last t2) by (rewrite !is_last_list, E; reflexivity).
  unfold atab_out_; split; cbn [shape cont]; [rewrite Eh, El; reflexivity|].
  rewrite <- El; destruct (is_last t1) eqn:L1; [intros [[[]|[]] V]; discriminate V|].
  intros _ _ _; change (to_list (rest t1) = to_list (rest t2)).
  rewrite (rest_list L1), (rest_list (eq_sym El)), E; reflexivity.
Qed.

Definition atab_out_c : Coalg (Memo NatF A) ATab := MkMorph atab_out_morph.

Lemma atab_out_fin
  : respects_relation atab_out_c (fun t => List.length (to_list t)) lt.
Proof.
  intros t; cbn [Morphism.app atab_out_c]; unfold atab_out_; cbn [shape cont].
  destruct (is_last t) eqn:L; [intros [[[]|[]] V]; discriminate V|].
  intros _; rewrite (to_list_out t), L; cbn [List.length]; lia.
Qed.

Definition atab_out : RCoalg (Memo NatF A) ATab := mk_wf_coalg wf_lt atab_out_fin.

Definition atab_in_ (x : App (Memo NatF A) ATab) : ATab :=
  match x with
  | MkCont (v, inl tt) _ => single v
  | MkCont (v, inr tt) k => push v (k (MkElem (inr tt) valid_inr_tt))
  end.

Lemma atab_in_morph : forall x y, x =e y -> atab_in_ x =e atab_in_ y.
Proof.
  intros [[v sx] kx] [[w sy] ky] [[Ev Es] Ek]; cbn in Ev, Es; apply leibniz in Ev; subst w.
  destruct sx as [[]|[]], sy as [[]|[]]; cbn in Es; try discriminate Es; try contradiction.
  - reflexivity.
  - change (to_list (push v (kx (MkElem (inr tt) valid_inr_tt)))
            = to_list (push v (ky (MkElem (inr tt) valid_inr_tt)))).
    rewrite !to_list_push; f_equal; apply Ek; reflexivity.
Qed.

Definition atab_in : App (Memo NatF A) ATab ~> ATab := MkMorph atab_in_morph.

Lemma atab_in_out : atab_in \o atab_out =e id.
Proof.
  intros t; change (to_list (atab_in_ (atab_out_ t)) = to_list t); unfold atab_out_.
  destruct (is_last t) eqn:L; cbn [atab_in_];
    [rewrite to_list_single | rewrite to_list_push]; rewrite (to_list_out t), L; reflexivity.
Qed.

Lemma atab_out_in : atab_out \o atab_in =e id.
Proof.
  intros [[v [[]|[]]] k]; change (atab_out_ (atab_in_ (MkCont (v, _) k)) =e MkCont (v, _) k);
    cbn [atab_in_]; unfold atab_out_; split; cbn [shape cont].
  - rewrite (head_list v), is_last_list, to_list_single; reflexivity.
  - intros e1 [[[]|[]] V]; discriminate V.
  - destruct (to_list_cons (k (MkElem (inr tt) valid_inr_tt))) as [w [l E]].
    rewrite (head_list v), is_last_list, to_list_push, E; reflexivity.
  - assert (L : is_last (push v (k (MkElem (inr tt) valid_inr_tt))) = false).
    { destruct (to_list_cons (k (MkElem (inr tt) valid_inr_tt))) as [w [l E]].
      rewrite is_last_list, to_list_push, E; reflexivity. }
    intros e1 [[[]|[]] V] _; try discriminate V.
    change (to_list (rest (push v (k (MkElem (inr tt) valid_inr_tt))))
            = to_list (k (MkElem (inr tt) V))).
    rewrite rest_list, to_list_push by exact L; cbn [tl].
    do 2 f_equal; apply elem_val_eq; reflexivity.
Qed.

Definition ATab_initial : Initial (Memo NatF A) ATab :=
  {| l_in := atab_in; l_out := atab_out; l_in_out := atab_in_out; l_out_in := atab_out_in |}.
Existing Instance ATab_initial.

End NatTables.
Arguments ATab : clear implicits.
#[export] Existing Instance ATab_initial.

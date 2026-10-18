Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

From Hylo Require Import Hylo.
Require Import Hylo.Utils.

From Stdlib Require Import List.
From Stdlib Require Import Uint63.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import PArray.

(* Memoisation tables for a container C, indexed by 'A' *)
(** The container below is equivalent to:
 * [ CoInductive MemoTable `(C : Cont Sc Pc) A
   := Cons { head : A; tail : App C (MemoTable C A) }.
   ]
 *)
Section MemoTable.
  Context `(G : Cont Sg Pg) `{setoid A}.

  Definition MemoShape : Type := A * Sg.
  Definition MemoPos := Pg.
  Instance Memo : Cont MemoShape MemoPos
    := { valid := valid \o pair (snd \o fst) snd }.

  Definition Table := LFix Memo.

  Definition ConsT (x : A * App G Table)
    : App Memo Table :=
    match x with
    | (a, MkCont sx kx) =>
        {| shape := (a, sx);
          cont := fun e : Container.Pos Memo (a, sx) =>
                    match e with
                    | MkElem e V => kx (MkElem e V)
                    end
        |}
    end.
  Lemma ConsT_morph : forall x y, x =e y -> ConsT x =e ConsT y.
  Proof.
    intros [ax [sx kx]] [ay [sy ky]] [Ea [St Kt]]; simpl in *.
    constructor; simpl; auto with ffix.
    intros [v1 V1] [v2 V2] Ev; simpl in *; subst; apply Kt; trivial.
  Qed.
  Definition Cons : A * App G Table ~> App Memo Table
    := Eval unfold ConsT in MkMorph ConsT_morph.

  Definition headT_ (t : Table) : A := fst (shape (l_out t)).
  Definition tailT_ (t : Table) : App G Table :=
    match l_out t with
    | {| shape := (a, st); cont := kt |} =>
        {| shape := st; cont := fun e =>
                                  match e with
                                  | MkElem v V => kt (MkElem v V)
                                  end
        |}
    end.
  Lemma headT_morph : forall x y, x =e y -> headT_ x =e headT_ y.
  Proof.
    intros [[[a sx] kx]] [[[b sy] ky]] [[]]; trivial.
  Qed.
  Definition headT := Eval unfold headT_ in MkMorph headT_morph.

  Lemma tailT_morph : forall x y, x =e y -> tailT_ x =e tailT_ y.
  Proof.
    intros [[[a sx] kx]] [[[b sy] ky]] [[Ea Es] Ek]; constructor; trivial.
    intros [v1 V1] [v2 V2] Eq; simpl in *; subst; apply Ek; trivial.
  Qed.
  Definition tailT := Eval unfold tailT_ in MkMorph tailT_morph.
End MemoTable.
Arguments Table {Sg}%_type_scope {Esh} {Pg}%_type_scope G A%_type_scope {H}.
Arguments Cons & {Sg}%_type_scope {Esh} {Pg}%_type_scope {G}
  {A}%_type_scope {_}.
Arguments headT {Sg}%_type_scope {Esh} {Pg}%_type_scope {G}
  {A}%_type_scope {H}.
Arguments tailT {Sg}%_type_scope {Esh} {Pg}%_type_scope {G}
  {A}%_type_scope {H}.

Definition dyna `{setoid A} `{setoid B} `{C : Cont Sc Pc}
  (a : App C (Table C A) ~> A) (c : RCoalg C B) : B ~> A
  := headT \o hylo (l_in \o Cons \o pair a id) c.

Definition NatF := Sum (K unit) Id.

Lemma valid_inr_tt : valid (F:=NatF) (inr tt, inr tt).
Proof. reflexivity. Qed.
Fixpoint lookupT `{setoid A} (x : nat) (t : Table NatF A) {struct x}: option A :=
  match x with
  | 0 => Some (headT_ t)
  | S y =>
      match tailT_ t with
      | MkCont st kt =>
          match st with
          | inl tt => fun _ => None
          | inr tt => fun k => lookupT y (k (MkElem (inr tt) valid_inr_tt))
          end kt
      end
  end.

Lemma lookupT_morph `{Leibniz A}
  : forall x y : nat, x =e y -> forall t t' : Table NatF A, t =e t' ->
    lookupT x t = lookupT y t'.
Proof.
  intros x y Exy; simpl in Exy; subst.
  induction y as [|y Ih]; intros t t' Rt; simpl.
  - f_equal; apply leibniz, (headT_morph Rt).
  - pose proof (tailT_morph Rt) as Tt; clear Rt.
    destruct tailT_ as [st kt], tailT_ as [st' kt'], Tt as [St Kt].
    simpl in *; destruct st as [[]|[]], st' as [[]|[]];
      try discriminate; try destruct St; trivial.
    apply Ih, Kt; trivial.
Qed.

Lemma nat_inl_empty : Container.Pos NatF (inl tt) -> False.
Proof. intros [[[]|[]] V]; discriminate V. Qed.

Definition out_int (n : int) : App NatF int :=
  MkCont (if (n =? 0)%uint63 then inl tt else inr tt) (fun _ => (n - 1)%uint63).

Lemma int_pred_lt (n : int) : (n =? 0)%uint63 = false ->
  Z.to_nat (Uint63.to_Z (n - 1)) < Z.to_nat (Uint63.to_Z n).
Proof.
  intros E; apply Uint63.eqb_false_spec in E.
  assert (Hn : Uint63.to_Z n <> 0%Z) by (intros H'; apply E, Uint63.to_Z_inj; exact H').
  pose proof (Uint63.to_Z_bounded n); rewrite Uint63.sub_spec.
  change (Uint63.to_Z 1) with 1%Z; rewrite Z.mod_small by lia; lia.
Qed.

Lemma out_int_fin : respects_relation out_int (fun n => Z.to_nat (Uint63.to_Z n)) lt.
Proof.
  intros n p; simpl in *; revert p; unfold out_int.
  destruct (n =? 0)%uint63 eqn:E; intros p; simpl in *.
  - destruct (nat_inl_empty p).
  - apply int_pred_lt, E.
Qed.

Definition out_int_c : RCoalg NatF int := mk_wf_coalg wf_lt out_int_fin.

Definition is_zero (n : int) : {(n =? 0)%uint63 = true} + {(n =? 0)%uint63 = false} :=
  if (n =? 0)%uint63 as b return {b = true} + {b = false} then left eq_refl else right eq_refl.

Section IntHylo.
  Context `{setoid B} (a : Alg NatF B).

  Fixpoint int_hylo_acc (n : int) (H : Acc lt (Z.to_nat (Uint63.to_Z n))) {struct H}
    : B :=
    match is_zero n with
    | left _ => a (MkCont (inl tt) (fun e => False_rect _ (nat_inl_empty e)))
    | right E =>
        let r := @int_hylo_acc (n - 1)%uint63 (Acc_inv H (int_pred_lt E)) in
        a (MkCont (inr tt) (fun _ => r))
    end.

  Arguments int_hylo_acc : clear implicits.

  Definition int_hylo (n : int) : B := int_hylo_acc n (wf_lt _).

  Lemma int_hylo_acc_irr_ k : forall n, Z.to_nat (Uint63.to_Z n) = k ->
    forall H1 H2 : Acc lt (Z.to_nat (Uint63.to_Z n)), int_hylo_acc n H1 = int_hylo_acc n H2.
  Proof.
    induction k as [k Ih] using (well_founded_ind wf_lt); intros n Ek [h1] [h2]; simpl.
    destruct (is_zero n) as [E|E]; trivial.
    erewrite (Ih (Z.to_nat (Uint63.to_Z (n - 1))));
      [reflexivity | subst k; apply int_pred_lt, E | reflexivity].
  Qed.

  Lemma int_hylo_acc_irr n (H1 H2 : Acc lt (Z.to_nat (Uint63.to_Z n)))
    : int_hylo_acc n H1 = int_hylo_acc n H2.
  Proof. exact (int_hylo_acc_irr_ eq_refl H1 H2). Qed.

  Lemma int_hylo_eq n
    : int_hylo n
      = match is_zero n with
        | left _ => a (MkCont (inl tt) (fun e => False_rect _ (nat_inl_empty e)))
        | right _ => a (MkCont (inr tt) (fun _ => int_hylo (n - 1)%uint63))
        end.
  Proof.
    unfold int_hylo at 1; destruct (wf_lt (Z.to_nat (Uint63.to_Z n))) as [h]; simpl.
    destruct (is_zero n) as [E|E]; trivial.
    unfold int_hylo; rewrite (int_hylo_acc_irr _ (wf_lt _)); reflexivity.
  Qed.

  Lemma hylo_out_int : hylo a out_int_c =e morph_of int_hylo.
  Proof.
    symmetry; apply hylo_uniq; intros n; simpl; rewrite int_hylo_eq.
    unfold out_int; destruct (is_zero n) as [E|E]; rewrite E; [|reflexivity].
    apply app_eq; split; [reflexivity|]; intros e; destruct (nat_inl_empty e).
  Qed.
End IntHylo.

Section NatTables.
  Context `{Leibniz A} (d : A).

(* Memo tables for [NatF] as lists *)
Definition to_list_alg_ (x : App (Memo NatF (A := A)) (list A)) : list A :=
  let (s, k) := x in
  match s as s return (Container.Pos (Memo NatF (A := A)) s -> list A) -> list A with
  | (a, inl _) => fun _ => a :: nil
  | (a, inr _) => fun k => a :: k (MkElem (inr tt) valid_inr_tt)
  end k.

Lemma to_list_alg_morph : forall x y, x =e y -> to_list_alg_ x =e to_list_alg_ y.
Proof.
  intros [[a sx] kx] [[b sy] ky] [[Ea Es] Ek]; apply leibniz in Ea; simpl in *; subst b.
  destruct sx as [[]|[]], sy as [[]|[]]; simpl in *; try contradiction;
    (split; [reflexivity|]); [trivial | apply Ek; reflexivity].
Qed.

Definition to_list : Table NatF A ~> list A :=
  cata (MkMorph to_list_alg_morph).

Lemma headT_to_list : headT =e hd d \o to_list.
Proof. intros [[[a [[]|[]]] k]]; reflexivity. Qed.

Definition list_alg_ (a : App NatF (list A) ~> A) (x : App NatF (list A))
  : list A :=
  a x :: match x with
         | MkCont (inl tt) _ => nil
         | MkCont (inr tt) k => k (MkElem (inr tt) valid_inr_tt)
         end.

Lemma list_alg_morph a : forall x y, x =e y -> list_alg_ a x =e list_alg_ a y.
Proof.
  intros x y E; pose proof (app_eq a E) as Ea; simpl in Ea.
  destruct x as [[[]|[]] kx], y as [[[]|[]] ky], E as [Es Ek];
    simpl in *; try contradiction; (split; [exact Ea|]); [trivial | apply Ek; reflexivity].
Qed.

Definition list_alg a : App NatF (list A) ~> list A := MkMorph (list_alg_morph a).

Lemma table_to_list `{setoid X} (c : RCoalg NatF X) (a : App NatF (Table NatF A) ~> A)
  (a' : App NatF (list A) ~> A) (Ha : a =e a' \o fmap to_list)
  : to_list \o hylo (l_in \o Cons \o pair a id) c =e hylo (list_alg a') c.
Proof.
  apply hylo_fusion_l; intros [[[]|[]] k]; simpl; split; try reflexivity;
    rewrite (Ha _); reflexivity.
Qed.

Lemma lookupT_to_list n t : lookupT n t = nth_error (to_list t) n.
Proof.
  revert t; induction n as [|n Ih]; intros [[[a [[]|[]]] k]]; simpl; trivial.
  all: try apply Ih.
  all: destruct n; reflexivity.
Qed.

(* Memo tables for [NatF] as arrays: [c] entries, the latest at [c - 1] *)
Definition ix (n : nat) : int := Uint63.of_Z (Z.of_nat n).

Lemma ix_spec n : (Z.of_nat n < wB)%Z -> Uint63.to_Z (ix n) = Z.of_nat n.
Proof. intros Hn; unfold ix; rewrite Uint63.of_Z_spec, Z.mod_small; lia. Qed.

Fixpoint tl_arr (t : array A) (c : nat) : list A :=
  match c with
  | 0 => nil
  | S c' => t.[ix c'] :: tl_arr t c'
  end.

Lemma nth_tl_arr t c j
  : nth_error (tl_arr t c) j = if Nat.ltb j c then Some t.[ix (c - 1 - j)] else None.
Proof.
  revert j; induction c as [|c Ih]; intros [|j]; simpl; trivial.
  - do 3 f_equal; lia.
  - rewrite Ih; change (Nat.ltb (S j) (S c)) with (Nat.ltb j c).
    destruct (Nat.ltb j c) eqn:E; trivial.
    apply Nat.ltb_lt in E; do 3 f_equal; lia.
Qed.

Lemma tl_arr_set t c v k
  : k <= c -> (Z.of_nat c < wB)%Z -> tl_arr t.[ix c <- v] k = tl_arr t k.
Proof.
  induction k as [|k Ih]; intros Hk Hc; simpl; trivial.
  rewrite Ih by lia; f_equal; apply get_set_other.
  intros E; apply (Logic.f_equal Uint63.to_Z) in E; rewrite !ix_spec in E by lia; lia.
Qed.

Lemma tl_arr_snoc t c v
  : (ix c <? length t)%uint63 = true -> (Z.of_nat c < wB)%Z ->
    tl_arr t.[ix c <- v] (S c) = v :: tl_arr t c.
Proof. intros H1 H2; simpl; rewrite get_set_same, tl_arr_set by (trivial || lia); reflexivity. Qed.

Lemma ix_to_nat (n : int) : ix (Z.to_nat (Uint63.to_Z n)) = n.
Proof.
  unfold ix; rewrite Z2Nat.id by (apply Uint63.to_Z_bounded); apply Uint63.of_to_Z.
Qed.

Lemma to_nat_succ (n : int) : (Uint63.to_Z n + 1 < wB)%Z ->
  Z.to_nat (Uint63.to_Z (n + 1)) = S (Z.to_nat (Uint63.to_Z n)).
Proof.
  intros Hn; pose proof (Uint63.to_Z_bounded n); rewrite Uint63.add_spec.
  change (Uint63.to_Z 1) with 1%Z; rewrite Z.mod_small by lia; lia.
Qed.

Definition tl : array A * int ~> list A :=
  morph_of (fun p => tl_arr (Datatypes.fst p) (Z.to_nat (Uint63.to_Z (Datatypes.snd p)))).

Lemma tl_snoc t c v : (c <? length t)%uint63 = true -> (Uint63.to_Z c + 1 < wB)%Z ->
  tl (t.[c <- v], (c + 1)%uint63) = v :: tl (t, c).
Proof.
  intros H1 H2; simpl; rewrite to_nat_succ by trivial.
  pose proof (Uint63.to_Z_bounded c).
  pose proof (tl_arr_snoc (t := t) (c := Z.to_nat (Uint63.to_Z c)) v) as T.
  rewrite ix_to_nat in T; apply T; [exact H1 | rewrite Z2Nat.id; lia].
Qed.

Definition arr_alg_ (N : int) (a : App NatF (array A * int) ~> A)
  (x : App NatF (array A * int)) : array A * int :=
  match x with
  | MkCont (inl tt) _ => ((make N d).[0%uint63 <- a x], 1%uint63)
  | MkCont (inr tt) k =>
      let (t, c) := k (MkElem (inr tt) valid_inr_tt) in (t.[c <- a x], (c + 1)%uint63)
  end.

Lemma arr_alg_morph N a : forall x y, x =e y -> arr_alg_ N a x =e arr_alg_ N a y.
Proof.
  intros x y E; pose proof (app_eq a E) as Ea; simpl in Ea.
  destruct x as [[[]|[]] kx], y as [[[]|[]] ky], E as [Es Ek];
    simpl in Es; cbn [cont shape] in Ek; try contradiction; unfold arr_alg_;
    rewrite (leibniz Ea); [reflexivity|].
  rewrite (leibniz (Ek _ (MkElem (inr tt) valid_inr_tt) eq_refl)); reflexivity.
Qed.

Definition arr_alg N a : App NatF (array A * int) ~> array A * int :=
  MkMorph (arr_alg_morph N a).

Lemma int_hylo_arr N (a'' : App NatF (array A * int) ~> A)
  (a' : App NatF (list A) ~> A) (Ha : a'' =e a' \o fmap tl) n
  : (Uint63.to_Z n < Uint63.to_Z N)%Z -> (Uint63.to_Z N <= Uint63.to_Z max_length)%Z ->
    Datatypes.snd (int_hylo (arr_alg N a'') n) = (n + 1)%uint63 /\
    length (Datatypes.fst (int_hylo (arr_alg N a'') n)) = N /\
    tl (int_hylo (arr_alg N a'') n) = int_hylo (list_alg a') n.
Proof.
  assert (Hm : (Uint63.to_Z max_length < wB)%Z) by (vm_compute; reflexivity).
  intros Hn HN.
  assert (Hlen : length (make N d) = N).
  { rewrite length_make; replace (N <=? max_length)%uint63 with true; trivial.
    symmetry; apply Uint63.leb_spec; lia. }
  remember (Z.to_nat (Uint63.to_Z n)) as k eqn:Ek; revert n Ek Hn.
  induction k as [|k Ih]; intros n Ek Hn; pose proof (Uint63.to_Z_bounded n);
    rewrite (int_hylo_eq (arr_alg N a'') n), (int_hylo_eq (list_alg a') n).
  - assert (E0 : n = 0%uint63) by (apply Uint63.to_Z_inj; change (Uint63.to_Z 0) with 0%Z; lia).
    subst n; destruct (is_zero 0%uint63) as [_|E0]; [|discriminate E0].
    simpl; rewrite length_set, Hlen; repeat split.
    simpl; rewrite get_set_same.
    + unfold list_alg_; f_equal; rewrite (leibniz (Ha _)); cbn [Morphism.app comp].
      apply leibniz, (app_eq a'); split; [reflexivity|].
      intros e; destruct (nat_inl_empty e).
    + rewrite Hlen; apply Uint63.ltb_spec; change (Uint63.to_Z (ix 0)) with 0%Z.
      change (Uint63.to_Z 0) with 0%Z in Hn; lia.
  - assert (E : (n =? 0)%uint63 = false).
    { apply Uint63.eqb_false_spec; intros E0; subst n; discriminate Ek. }
    assert (Hn0 : (0 < Uint63.to_Z n)%Z).
    { apply Uint63.eqb_false_spec in E.
      assert (Uint63.to_Z n <> 0%Z) by (intros E0; apply E, Uint63.to_Z_inj; exact E0); lia. }
    destruct (is_zero n) as [E'|_]; [rewrite E in E'; discriminate E'|].
    assert (Ek' : k = Z.to_nat (Uint63.to_Z (n - 1))).
    { pose proof (int_pred_lt E). rewrite Uint63.sub_spec in *.
      change (Uint63.to_Z 1) with 1%Z in *; rewrite Z.mod_small in * by lia; lia. }
    assert (Hn' : (Uint63.to_Z (n - 1) < Uint63.to_Z N)%Z).
    { rewrite Uint63.sub_spec; change (Uint63.to_Z 1) with 1%Z.
      rewrite Z.mod_small by lia; lia. }
    destruct (Ih _ Ek' Hn') as [Ec [El Et]].
    destruct (int_hylo (arr_alg N a'') (n - 1)%uint63) as [t c]; cbn -[tl wB Uint63.to_Z int_hylo] in *.
    assert (Ec' : c = n).
    { subst c; apply Uint63.to_Z_inj; rewrite Uint63.add_spec, Uint63.sub_spec.
      change (Uint63.to_Z 1) with 1%Z; rewrite (Z.mod_small (_ - 1)) by lia.
      rewrite Z.mod_small by lia; lia. }
    clear Ec; subst c; rewrite length_set; repeat split; trivial.
    rewrite tl_snoc.
    + unfold list_alg_; f_equal; [| exact Et].
      rewrite (leibniz (Ha _)); cbn [Morphism.app comp].
      apply leibniz, (app_eq a'); split; [reflexivity|]; intros; apply eq_eqRel, Et.
    + rewrite El; apply Uint63.ltb_spec; lia.
    + lia.
Qed.

Lemma dyna_array (a'' : App NatF (array A * int) ~> A)
  (a' : App NatF (list A) ~> A) (Ha : a'' =e a' \o fmap tl) n
  : (Uint63.to_Z n < Uint63.to_Z max_length)%Z ->
    hd d (int_hylo (list_alg a') n)
    = (Datatypes.fst (int_hylo (arr_alg (n + 1)%uint63 a'') n)).[n].
Proof.
  intros Hn; pose proof (Uint63.to_Z_bounded n).
  assert (Hm : (Uint63.to_Z max_length < wB)%Z) by (vm_compute; reflexivity).
  assert (HN : Uint63.to_Z (n + 1) = (Uint63.to_Z n + 1)%Z).
  { rewrite Uint63.add_spec; change (Uint63.to_Z 1) with 1%Z; apply Z.mod_small; lia. }
  destruct (int_hylo_arr (N := (n + 1)%uint63) Ha (n := n)) as [Ec [_ Et]]; [lia | lia |].
  rewrite <- Et; destruct (int_hylo (arr_alg (n + 1)%uint63 a'') n) as [t c].
  simpl in *; subst c; rewrite to_nat_succ by lia; simpl; rewrite ix_to_nat; reflexivity.
Qed.

End NatTables.

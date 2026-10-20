Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Hylo.
Require Import Hylo.Utils.

From Stdlib Require Import Uint63.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import ZifyUint63.

(** * Dynamorphisms
  *
  * Memo tables for a container [G] with entries in [A] are initial algebras of
  * [Memo G A] ([X = A * G X]). [dyna] works for any of them: [LFix (Memo G A)]
  * ([LFix_initial]) is the default, and [dyna_iso] replaces one by another. *)
Section MemoDef.
  Context `(G : Cont Sg Pg) `{setoid A}.

  Definition MemoShape : Type := A * Sg.
  Definition MemoPos := Pg.
  Instance Memo : Cont MemoShape MemoPos
    := { valid := valid \o pair (snd \o fst) snd }.

  Definition mcons `{setoid X} : A * App G X ~> App Memo X :=
    morph_of (fun x =>
    match x with
    | (a, MkCont sx kx) =>
        MkCont (a, sx) (fun e : Container.Pos Memo (a, sx) =>
                          match e with MkElem e V => kx (MkElem e V) end)
    end).

  Definition mhead `{setoid X} : App Memo X ~> A
    := morph_of (fun x => Datatypes.fst (shape x)).

  Lemma mcons_nat `{setoid X} `{setoid Y} (f : X ~> Y)
    : fmap f \o mcons =e mcons \o pair fst (fmap f \o snd).
  Proof.
    intros [a [s k]]; split; [reflexivity|].
    intros [v1 V1] [v2 V2] Ev; cbn in Ev; subst v2; cbn.
    replace V2 with V1 by apply bool_irrelevance; reflexivity.
  Qed.

  Lemma mhead_fmap `{setoid X} `{setoid Y} (f : X ~> Y)
    : mhead \o fmap f =e mhead.
  Proof. intros x; reflexivity. Qed.
End MemoDef.
Arguments mcons_nat {Sg Esh Pg} G A {H X H0 Y H1} f _.
Arguments mhead_fmap {Sg Esh Pg} G A {H X H0 Y H1} f _.
Arguments Memo {Sg Esh Pg} G A {H}.
Arguments mcons {Sg Esh Pg G A H X _}.
Arguments mhead {Sg Esh Pg G A H X _}.

Definition dyna `{setoid A} `{setoid B} `{G : Cont Sg Pg} `{eT : setoid T}
  `{!Initial (Memo G A) T} (a : App G T ~> A) (c : RCoalg G B) : B ~> A
  := mhead \o l_out \o hylo (l_in \o mcons \o pair a id) c.

(** [dyna] does not depend on the memo table *)
Theorem dyna_iso `{setoid A} `{setoid B} `{G : Cont Sg Pg}
  `{eT : setoid T} `{!Initial (Memo G A) T}
  `{eU : setoid U} `{!Initial (Memo G A) U} (a : App G T ~> A) (c : RCoalg G B)
  : dyna a c =e dyna (a \o fmap (iso U T)) c.
Proof.
  unfold dyna; erewrite <- (hylo_fusion_l c (f2 := iso U T)).
  - arewrite (iso_out U T); arewrite (mhead_fmap G A (iso U T)).
    reflexivity.
  - arewrite (iso_in U T); arewrite (mcons_nat G A (iso U T)).
    intros x; reflexivity.
Qed.

(** * Dynamorphisms and hylomorphisms
  *
  * [table c f] is the table of [f] along [c]: each node holds [f b] and the
  * tables of the children of [b]. *)
Section Table.
  Context `{G : Cont Sg Pg} `{setoid A} `{setoid B}
    (c : RCoalg G B) (f : B ~> A).

  Lemma table_rec : RecP (mcons \o pair f c).
  Proof.
    intros b; induction (terminating c b) as [b _ Ih]; constructor; cbn.
    destruct (c b) as [s k]; intros [v V]; apply Ih.
  Defined.

  Context `{eT : setoid T} `{!Initial (Memo G A) T}.

  Definition table : B ~> T :=
    rana (Rec (coalg := mcons \o pair f c) table_rec).

  Lemma table_unfold : table =e l_in \o mcons \o pair f (fmap table \o c).
  Proof.
    unfold table at 1; rewrite rana_unfold; fold table.
    arewrite (mcons_nat G A table); intros x; reflexivity.
  Qed.

  Lemma mhead_table : mhead \o l_out \o table =e f.
  Proof.
    rewrite table_unfold at 1; arewrite l_out_in.
    intros x; cbn; destruct (c x); reflexivity.
  Qed.
End Table.
Arguments table {Sg Esh Pg G A H B H0} c f {T eT _}.

(** Memoising with the same coalgebra: the algebra reads the heads of the
  * children's tables *)
Theorem dyna_heads `{setoid A} `{setoid B} `{G : Cont Sg Pg}
  `{eT : setoid T} `{!Initial (Memo G A) T}
  (a : App G A ~> A) (c : RCoalg G B)
  : hylo a c =e dyna (a \o fmap (mhead \o l_out)) c.
Proof.
  unfold dyna; symmetry; apply hylo_fusion_l; arewrite l_out_in.
  intros [s k]; reflexivity.
Qed.

(** Paths: positions followed by [step] (a coalgebra, or [l_out] on tables) *)
Section Walk.
  Context `{F : Cont Sh P} {X : Type} (step : X -> App F X).

  Definition at_pos (x : App F X) (p : P) : option X :=
    match Bool.bool_dec (valid (shape x, p)) true with
    | left V => Some (cont x (MkElem p V))
    | right _ => None
    end.

  Fixpoint walk (x : X) (ps : list P) : option X :=
    match ps with
    | nil => Some x
    | cons p ps =>
        match at_pos (step x) p with Some y => walk y ps | None => None end
    end.
End Walk.

(** Paths starting at a layer (of any container with the same positions): the
  * first position selects a child *)
Definition walk_from `{F : Cont Sh P} `{F' : Cont Sh' P} {X : Type}
  (step : X -> App F X) (y : App F' X) (ps : list P) : option X :=
  match ps with
  | nil => None
  | cons p ps =>
      match at_pos y p with Some x => walk step x ps | None => None end
  end.

Lemma at_pos_eq `{F : Cont Sh P} `{setoid X} (x y : App F X) p
  : x =e y -> at_pos x p =e at_pos y p.
Proof.
  intros [Es Ek]; unfold at_pos.
  assert (V : valid (shape x, p) = valid (shape y, p))
    by exact (app_eq valid (x := (shape x, p)) (y := (shape y, p))
                (conj Es eq_refl)).
  destruct (Bool.bool_dec (valid (shape x, p)) true),
    (Bool.bool_dec (valid (shape y, p)) true);
    cbn; [apply Ek; reflexivity | congruence | congruence | exact I].
Qed.

Lemma at_pos_mcons `{G : Cont Sg Pg} `{setoid A} `{setoid X} `{setoid Y}
  (h : X ~> Y) a x p
  : at_pos (mcons (a, fmap h x) : App (Memo G A) Y) p
    = option_map h (at_pos x p).
Proof.
  unfold at_pos; cbn; destruct (Bool.bool_dec _ _),
    (Bool.bool_dec (valid (shape x, p)) true); try reflexivity; contradiction.
Qed.

(** A map [h] between steps that commutes with one step commutes with walks *)
Lemma walk_hom `{F : Cont Sh P} `{F' : Cont Sh' P} `{setoid X} `{setoid Y}
  (sx : X -> App F X) (sy : Y -> App F' Y) (h : X -> Y)
  (Hh : forall x y p,
      y =e h x -> at_pos (sy y) p =e option_map h (at_pos (sx x) p))
  : forall ps x y, y =e h x -> walk sy y ps =e option_map h (walk sx x ps).
Proof.
  induction ps as [|p ps Ih]; intros x y E; [exact E|]; cbn [walk].
  specialize (Hh x y p E); destruct (at_pos (sx x) p), (at_pos (sy y) p);
    cbn in Hh |- *; try contradiction; [apply Ih, Hh | exact I].
Qed.

Lemma option_map_eq `{setoid X} `{setoid Y} (f : X ~> Y) (o1 o2 : option X)
  : o1 =e o2 -> option_map f o1 =e option_map f o2.
Proof. destruct o1, o2; cbn; try contradiction; [apply app_eq | trivial]. Qed.

#[export] Instance option_map_proper `{setoid X} `{setoid Y} (f : X ~> Y)
  : Proper (eqRel ==> eqRel) (option_map f) := option_map_eq f.

Lemma option_map_id {X} (o : option X) : option_map (fun x => x) o = o.
Proof. destruct o; reflexivity. Qed.

Lemma at_pos_fmap `{F : Cont Sh P} `{setoid X} `{setoid Y}
  (h : X ~> Y) (x : App F X) p
  : at_pos (fmap h x) p = option_map h (at_pos x p).
Proof. unfold at_pos; cbn; destruct (Bool.bool_dec _ _); reflexivity. Qed.

Lemma walk_from_hom `{F : Cont Sh P} `{F' : Cont Sh' P}
  `{F1 : Cont Sh1 P} `{F2 : Cont Sh2 P} `{setoid X} `{setoid Y}
  (sx : X -> App F X) (sy : Y -> App F' Y) (h : X -> Y)
  (Hh : forall x y p,
      y =e h x -> at_pos (sy y) p =e option_map h (at_pos (sx x) p))
  (y : App F1 X) (y' : App F2 Y)
  (Hy : forall p, at_pos y' p =e option_map h (at_pos y p)) ps
  : walk_from sy y' ps =e option_map h (walk_from sx y ps).
Proof.
  destruct ps as [|p ps]; [exact I|]; cbn [walk_from]; specialize (Hy p).
  destruct (at_pos y p), (at_pos y' p); cbn in Hy |- *; try contradiction;
    [apply walk_hom; assumption | exact I].
Qed.

(** [table c f] commutes with a step of [c] *)
Lemma table_step `{G : Cont Sg Pg} `{setoid A} `{setoid B} `{eT : setoid T}
  `{!Initial (Memo G A) T} (c : RCoalg G B) (f : B ~> A)
  : forall x y p, y =e table c f x ->
    at_pos (l_out y) p =e option_map (table c f) (at_pos (c x) p).
Proof.
  intros x y p E; rewrite <- (at_pos_mcons _ (f x)); apply at_pos_eq.
  rewrite E, (table_unfold c f x); apply l_out_in.
Qed.

(** Paths [Pa] from a layer of [G], along steps into containers with the same
  * positions. [pwalk_hom]: a map between steps that commutes with one step
  * commutes with walks. Lists of positions are paths for any [G]. *)
Class Paths `(G : Cont Sg P) (Pa : Type) := {
  pwalk : forall `{F : Cont Sh P} `{setoid X},
      (X -> App F X) -> App G X -> Pa -> option X;
  pwalk_hom : forall `{F : Cont Sh P} `{F' : Cont Sh' P} `{setoid X} `{setoid Y}
    (sx : X -> App F X) (sy : Y -> App F' Y) (h : X ~> Y),
    (forall x y p,
        y =e h x -> at_pos (sy y) p =e option_map h (at_pos (sx x) p)) ->
    forall (y : App G X) (y' : App G Y),
    (forall p, at_pos y' p =e option_map h (at_pos y p)) ->
    forall k, pwalk sy y' k =e option_map h (pwalk sx y k)
}.

#[export] Instance list_paths `{G : Cont Sg P} : Paths G (list P).
Proof.
  refine {| pwalk Sh Esh F X eX := walk_from (F := F) (F' := G) (X := X) |}.
  intros; apply walk_from_hom; assumption.
Defined.

(** Changing the coalgebra: [alg] reads the results it needs through a [look]
  * at paths along [e]. [look_rec] recomputes them, [look_tbl] reads them from
  * the table. *)
Section Reenumerate.
  Context `{setoid A} `{setoid B} `{G : Cont Sg Pg}
    `{eU : setoid U} `{!Initial (Memo G A) U} `{!Paths G Pa}.

  Definition look_rec (e : RCoalg G B) (g : B -> A) (b : B) (k : Pa)
    : option A :=
    option_map g (pwalk e (e b) k).

  Definition look_tbl_ (x : App G U) (k : Pa) : option A :=
    option_map (mhead \o l_out) (pwalk l_out x k).

  Lemma look_tbl_eq : forall x y, x =e y -> look_tbl_ x =e look_tbl_ y.
  Proof.
    intros x y E ps; apply option_map_eq; symmetry.
    rewrite <- (option_map_id (pwalk l_out x ps)).
    apply (pwalk_hom (h := id)); intros; rewrite option_map_id.
    - apply at_pos_eq, app_eq; assumption.
    - symmetry; apply at_pos_eq, E.
  Qed.

  Definition look_tbl : App G U ~> (Pa -> option A) := MkMorph look_tbl_eq.

  (** The invariant: looking into the table is recomputing *)
  Lemma look_table (e : RCoalg G B) (g : B ~> A) b
    : look_tbl (fmap (table e g) (e b)) =e look_rec e g b.
  Proof.
    intros ps; etransitivity.
    - apply option_map_eq, (pwalk_hom (table_step (c := e) (f := g)))
        with (y := e b); intros p; rewrite at_pos_fmap; reflexivity.
    - unfold look_rec; destruct (pwalk e (e b) ps);
        [exact (mhead_table e g _) | exact I].
  Qed.

  Theorem reenumerate `{F : Cont Sf Pf} (an : App F A ~> A) (cn : RCoalg F B)
    (e : RCoalg G B) (alg : (Pa -> option A) ~> A)
    (Hlook : forall (g : B ~> A) b,
        an (fmap g (cn b)) =e alg (look_rec e g b))
    : hylo an cn =e dyna (alg \o look_tbl) e.
  Proof.
    unfold dyna; rewrite <- (hylo_uniq_r (f := table e (hylo an cn))).
    - symmetry; apply mhead_table.
    - rewrite table_unfold at 1; intros b; cbn [app comp].
      apply (app_eq l_in), (app_eq mcons); split; [|reflexivity].
      rewrite (hylo_unr an cn b); etransitivity; [apply (Hlook _ b)|].
      apply (app_eq alg); symmetry; apply look_table.
  Qed.
End Reenumerate.

(** * Memo tables for sequences *)
Definition NatF := Sum (K unit) Id.

Lemma valid_inr_tt : valid (F:=NatF) (inr tt, inr tt).
Proof. reflexivity. Qed.

Lemma nat_inl_empty : Container.Pos NatF (inl tt) -> False.
Proof. intros [[[]|[]] V]; discriminate V. Qed.

(** Sharing: [hylo] passes the recursive call as the continuation [k], which
  * recomputes it on every use. In [l_in \o mcons \o pair a id] the child is
  * used twice (by [a], and as the rest of the table), so the extracted code
  * would be exponential; [memo_alg] binds it once. *)
Section NatMemo.
  Context `{setoid A} `{eT : setoid T} `{!Initial (Memo NatF A) T}.

  Definition memo_alg_ (a : App NatF T ~> A) (x : App NatF T) : T :=
    match x with
    | MkCont (inl tt) k =>
        l_in (mcons (a (MkCont (inl tt) k), MkCont (inl tt) k))
    | MkCont (inr tt) k =>
        let r := k (MkElem (inr tt) valid_inr_tt) in
        l_in (mcons (a (MkCont (inr tt) (fun _ => r)),
                     MkCont (inr tt) (fun _ => r)))
    end.

  Lemma memo_alg_eq (a : App NatF T ~> A) x
    : memo_alg_ a x =e (l_in \o mcons \o pair a id) x.
  Proof.
    destruct x as [[[]|[]] k]; [reflexivity|]; cbn [memo_alg_ app comp].
    assert (E : MkCont (inr tt) (fun _ => k (MkElem (inr tt) valid_inr_tt))
                =e MkCont (inr tt) k).
    { split; [reflexivity|]; intros [[[]|[]] V1] [[[]|[]] V2] _;
        try discriminate V1; try discriminate V2; cbn.
      replace V2 with valid_inr_tt by apply bool_irrelevance; reflexivity. }
    apply (app_eq l_in), (app_eq mcons); split; [apply (app_eq a)|]; exact E.
  Qed.

  Definition memo_alg a : Alg NatF T := morph_of (memo_alg_ a).

  Lemma dyna_memo `{setoid B} (a : App NatF T ~> A) (c : RCoalg NatF B)
    : dyna a c =e mhead \o l_out \o hylo (memo_alg a) c.
  Proof.
    intros x; cbn [app comp].
    apply (app_eq mhead), (app_eq (coalg (l_out (T := T)))); symmetry.
    exact (app_eq hylo (fun y => memo_alg_eq a y) c x).
  Qed.
End NatMemo.

(** Counting down on machine integers *)
Definition out_int (n : int) : App NatF int :=
  MkCont (if (n =? 0)%uint63 then inl tt else inr tt) (fun _ => (n - 1)%uint63).

Lemma int_pred_lt (n : int) : (n =? 0)%uint63 = false ->
  Z.to_nat (Uint63.to_Z (n - 1)) < Z.to_nat (Uint63.to_Z n).
Proof. lia. Qed.

Lemma out_int_fin
  : respects_relation out_int (fun n => Z.to_nat (Uint63.to_Z n)) lt.
Proof.
  intros n p; simpl in *; revert p; unfold out_int.
  destruct (n =? 0)%uint63 eqn:E; intros p; simpl in *.
  - destruct (nat_inl_empty p).
  - apply int_pred_lt, E.
Qed.

Definition out_int_c : RCoalg NatF int := mk_wf_coalg wf_lt out_int_fin.

(** * Paths along count-downs are lengths
  *
  * [iwalk step j x] takes [j] steps from [x] by recursion on [out_int_c]. *)
Section IntPaths.
  Context `{F : Cont Sh (False + unit)} `{setoid X} (step : X -> App F X).

  Definition iwalk_alg_ (x : App NatF (X -> option X)) (y : X) : option X :=
    match x with
    | MkCont (inl tt) _ => Some y
    | MkCont (inr tt) k =>
        match at_pos (step y) (inr tt) with
        | Some z => k (MkElem (inr tt) valid_inr_tt) z
        | None => None
        end
    end.

  Lemma iwalk_alg_eq : forall x y, x =e y -> iwalk_alg_ x =e iwalk_alg_ y.
  Proof.
    intros [[[]|[]] kx] [[[]|[]] ky] [Es Ek] y; cbn in Es; try contradiction;
      cbn; [apply e_refl|].
    destruct (at_pos (step y) (inr tt)); [apply Ek; reflexivity | exact I].
  Qed.

  Definition iwalk : int ~> (X -> option X) :=
    hylo (MkMorph iwalk_alg_eq) out_int_c.

  Lemma iwalk_unfold j x : iwalk j x =e iwalk_alg_ (fmap iwalk (out_int j)) x.
  Proof. exact (hylo_unr (MkMorph iwalk_alg_eq) out_int_c j x). Qed.

  Definition iwalk_from (y : App NatF X) (j : int) : option X :=
    if (j =? 0)%uint63 then None
    else match at_pos y (inr tt) with
         | Some x => iwalk (j - 1)%uint63 x
         | None => None
         end.
End IntPaths.

Lemma iwalk_hom `{F : Cont Sh (False + unit)} `{F' : Cont Sh' (False + unit)}
  `{setoid X} `{setoid Y} (sx : X -> App F X) (sy : Y -> App F' Y) (h : X ~> Y)
  (Hh : forall x y p,
      y =e h x -> at_pos (sy y) p =e option_map h (at_pos (sx x) p))
  : forall j x y, y =e h x -> iwalk sy j y =e option_map h (iwalk sx j x).
Proof.
  intros j; remember (Z.to_nat (Uint63.to_Z j)) as n eqn:En; revert j En.
  induction n as [|n Ih]; intros j En x y E;
    rewrite (iwalk_unfold sy j y), (iwalk_unfold sx j x);
    unfold out_int; destruct (j =? 0)%uint63 eqn:Ej; cbn -[iwalk];
    [exact E | exfalso; lia | exact E |].
  specialize (Hh x y (inr tt) E); destruct (at_pos (sx x) _), (at_pos (sy y) _);
    cbn in Hh |- *; try contradiction; [apply Ih; [lia | exact Hh] | exact I].
Qed.

#[export] Instance int_paths : Paths NatF int.
Proof.
  refine {| pwalk Sh Esh F X eX := iwalk_from (F := F) (X := X) |}.
  intros * Hh y y' Hy j; unfold iwalk_from.
  destruct (j =? 0)%uint63; [exact I|].
  specialize (Hy (inr tt)); destruct (at_pos y _), (at_pos y' _);
    cbn in Hy |- *; try contradiction; try exact I; apply iwalk_hom; assumption.
Defined.

(* Case analysis on the tests in [if]s, closing branches by [lia] *)
Ltac int_cases :=
  repeat match goal with
         | |- context [if ?c then _ else _] => destruct c eqn:?
         end;
  cbn [option_map];
  first [reflexivity | exfalso; lia | f_equal; lia | do 2 f_equal; lia].

Lemma iwalk_down : forall j b,
  iwalk out_int_c j b = if (j <=? b)%uint63 then Some (b - j)%uint63 else None.
Proof.
  intros j; remember (Z.to_nat (Uint63.to_Z j)) as n eqn:En; revert j En.
  induction n as [|n Ih]; intros j En b;
    rewrite (leibniz (iwalk_unfold _ j b)); unfold out_int;
    destruct (j =? 0)%uint63 eqn:Ej; cbn -[iwalk]; unfold at_pos; cbn -[iwalk];
    destruct (b =? 0)%uint63 eqn:Eb; cbn -[iwalk];
    try rewrite (Ih (j - 1)%uint63) by lia; int_cases.
Qed.

(** Looking [j] down the count-down from [b] recomputes [b - j] *)
Lemma look_down `{setoid A} (g : int -> A) b j
  : look_rec out_int_c g b j
    = if ((0 <? j)%uint63 && (j <=? b)%uint63)%bool then Some (g (b - j)%uint63)
      else None.
Proof.
  unfold look_rec; cbn [pwalk int_paths]; unfold iwalk_from.
  destruct (j =? 0)%uint63 eqn:Ej; cbn -[iwalk]; unfold at_pos; cbn -[iwalk];
    destruct (b =? 0)%uint63 eqn:Eb; cbn -[iwalk]; try rewrite iwalk_down;
    int_cases.
Qed.

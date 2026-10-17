From Paco Require Import paco.

Unset Auto Template Polymorphism.

(** [coind CH] starts a proof by coinduction on a goal
    [forall xs, Hs -> R a1 .. an], where [R] unfolds to [pacoN gf r]
    (N = 1..5).

    The quantified [xs], the premises [Hs], and every argument [ai] that is a
    variable are generalized. Writing [Ps] for all of these, [coind CH] leaves
    a fresh relation [r], the coinduction hypothesis
    [CH : forall Ps, r a1 .. an], and the goal
    [forall Ps, pacoN gf r a1 .. an].

    The goal is generalized with the relation
    [l u1 .. un := forall Y, (forall Ps, Y a1 .. an) -> Y u1 .. un]
    and closed with [pacoN_acc]. *)

Inductive _co_marker := _co_marker_constr.

(* Introduce the premises of the goal after a fresh marker. *)
Ltac co_move :=
  let M := fresh "M" in
  pose proof _co_marker_constr as M;
  repeat
    lazymatch goal with
    | [|- forall nm : _, _] => let H := fresh nm in intro H
    end.

(* Revert every hypothesis after the marker, then clear the marker. *)
Ltac co_revert :=
  lazymatch goal with
  | [x : ?T |- _] =>
    lazymatch T with
    | _co_marker => clear x
    | _ => revert x; co_revert
    end
  end.

(* Clear every hypothesis after the marker, and the marker. *)
Ltac co_clear :=
  lazymatch goal with
  | [x : ?T |- _] =>
    lazymatch T with
    | _co_marker => clear x
    | _ => clear x; co_clear
    end
  end.

(* If [a] is a variable, move it right after the marker, so that it is
   generalized. [move a after M] only does this when [a] is above the marker;
   when [a] is below it, [move a before M] does. *)
Ltac co_float a :=
  tryif is_var a then
    lazymatch goal with
    | [M : _co_marker |- _] =>
      first
        [ assert_succeeds (co_revert; let T := type of a in idtac);
          try (move a after M)
        | try (move a before M) ]
    end
  else idtac.

(* The goal is [forall Ps, R as], with [K : forall Y, F Y -> forall Ps, Y as]
   and [H : forall us, l us -> R us]. Introduce [Ps], passing each one to [K],
   until [K : forall Y, F Y -> Y as], which proves [l as]. *)
Ltac co_lock K H :=
  lazymatch goal with
  | [|- forall _ : _, _] =>
    let p := fresh "p" in
    intro p;
    let K' := fresh "K" in
    pose proof (fun Y HY => K Y HY p) as K';
    clear K; co_lock K' H
  | _ => apply H; exact K
  end.

(* Prove [F R] (that is, [forall Ps, R as]) from
   [H : forall us, l us -> R us]. *)
Ltac co_from F H :=
  hnf;
  let K := fresh "K" in
  pose proof (fun Y (HY : F Y) => HY) as K;
  co_lock K H.

(* The goal is [R as], with [Xv := R] and the generalized hypotheses after
   the marker. [cut_tac F T] states [forall us, l us -> Xv us] for the
   relation [l] built from [F] (with [Y : T]); [acc_tac] applies
   [pacoN_acc]. *)
Ltac co_body Xv cut_tac acc_tac CH :=
  lazymatch goal with
  (* [Xv] is last: this moves it above [M] *)
  | [M : _co_marker |- _] => move Xv after M
  end;
  co_revert;
  let G := lazymatch goal with [|- ?G] => G end in
  let F := lazymatch (eval pattern Xv in G) with ?F _ => F end in
  let T := type of Xv in
  cut_tac F T;
  [ let Hc := fresh "Hc" in
    intro Hc; co_from F Hc
  | subst Xv; acc_tac;
    let r := fresh "r" in
    let INC := fresh "INC" in
    let CHr := fresh "CHr" in
    intros r INC CHr; clear INC;
    assert (CH : F r) by co_from F CHr;
    hnf in CH; clear CHr;
    let M := fresh "M" in
    pose proof _co_marker_constr as M;
    intros;
    lazymatch goal with
    | [Hl : _ |- _] => apply Hl
    end;
    co_clear; hnf
  ].

Ltac co_shape1 CH :=
  lazymatch goal with
  | [|- ?R ?a1] =>
    co_float a1;
    let Xv := fresh "R" in
    set (Xv := R);
    co_body Xv
      ltac:(fun F T => cut (forall u1, (forall Y : T, F Y -> Y u1) -> Xv u1))
      ltac:(apply paco1_acc) CH
  end.

Ltac co_shape2 CH :=
  lazymatch goal with
  | [|- ?R ?a1 ?a2] =>
    co_float a2; co_float a1;
    let Xv := fresh "R" in
    set (Xv := R);
    co_body Xv
      ltac:(fun F T =>
              cut (forall u1 u2, (forall Y : T, F Y -> Y u1 u2) -> Xv u1 u2))
      ltac:(apply paco2_acc) CH
  end.

Ltac co_shape3 CH :=
  lazymatch goal with
  | [|- ?R ?a1 ?a2 ?a3] =>
    co_float a3; co_float a2; co_float a1;
    let Xv := fresh "R" in
    set (Xv := R);
    co_body Xv
      ltac:(fun F T =>
              cut (forall u1 u2 u3,
                      (forall Y : T, F Y -> Y u1 u2 u3) -> Xv u1 u2 u3))
      ltac:(apply paco3_acc) CH
  end.

Ltac co_shape4 CH :=
  lazymatch goal with
  | [|- ?R ?a1 ?a2 ?a3 ?a4] =>
    co_float a4; co_float a3; co_float a2; co_float a1;
    let Xv := fresh "R" in
    set (Xv := R);
    co_body Xv
      ltac:(fun F T =>
              cut (forall u1 u2 u3 u4,
                      (forall Y : T, F Y -> Y u1 u2 u3 u4) -> Xv u1 u2 u3 u4))
      ltac:(apply paco4_acc) CH
  end.

Ltac co_shape5 CH :=
  lazymatch goal with
  | [|- ?R ?a1 ?a2 ?a3 ?a4 ?a5] =>
    co_float a5; co_float a4; co_float a3; co_float a2; co_float a1;
    let Xv := fresh "R" in
    set (Xv := R);
    co_body Xv
      ltac:(fun F T =>
              cut (forall u1 u2 u3 u4 u5,
                      (forall Y : T, F Y -> Y u1 u2 u3 u4 u5) ->
                      Xv u1 u2 u3 u4 u5))
      ltac:(apply paco5_acc) CH
  end.

Ltac coind CH :=
  co_move;
  first [ co_shape1 CH | co_shape2 CH | co_shape3 CH | co_shape4 CH
        | co_shape5 CH ].

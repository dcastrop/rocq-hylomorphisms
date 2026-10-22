Set Warnings "-bad-template-constraint,-disj-pattern-notation".
Set Warnings "-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Core.
Require Import Hylo.Schemes.Hylomorphisms.

From Stdlib Require Import Uint63.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import ZifyUint63.

(** * Loops

  * [loop n body (i, s)] runs [body i], [body (i + 1)], ..., [body (n - 1)] on
  * the state [s]. It is a hylomorphism whose coalgebra does the work and whose
  * algebra returns the final state, so the recursive call is a tail call. *)
Section LoopDef.
  Context `{eS : setoid St}.

  (* [inl s]: done, with the final state; [inr tt]: one more step *)
  Definition LoopF := Sum (K St) Id.

  Lemma loop_step_valid : valid (F := LoopF) (inr tt, inr tt).
  Proof. reflexivity. Qed.

  Lemma loop_done_empty s : Container.Pos LoopF (inl s) -> False.
  Proof. intros [[[]|[]] V]; discriminate V. Qed.

  Definition loop_alg_ (x : App LoopF St) : St :=
    match x with
    | MkCont (inl s) _ => s
    | MkCont (inr tt) k => k (MkElem (inr tt) loop_step_valid)
    end.

  Lemma loop_alg_eq : forall x y, x =e y -> loop_alg_ x =e loop_alg_ y.
  Proof.
    intros [[s|[]] kx] [[t|[]] ky] [Es Ek]; cbn in Es; try contradiction;
      [exact Es | apply Ek; reflexivity].
  Qed.

  Definition loop_alg : Alg LoopF St := MkMorph loop_alg_eq.

  Context (n : int) (body : int -> St ~> St).

  Definition loop_c_ (x : int * St) : App LoopF (int * St) :=
    let (i, s) := x in
    if (i <? n)%uint63
    then MkCont (inr tt) (fun _ => ((i + 1)%uint63, body i s))
    else MkCont (inl s) (fun e => False_rect _ (loop_done_empty e)).

  Lemma loop_c_eq : forall x y, x =e y -> loop_c_ x =e loop_c_ y.
  Proof.
    intros [i s] [j t] [Ei Es]; cbn in Ei; subst j; unfold loop_c_.
    destruct (i <? n)%uint63; split; cbn; try exact Es; trivial.
    - intros; split; [reflexivity | apply app_eq, Es].
    - intros e; destruct (loop_done_empty e).
  Qed.

  Lemma loop_c_fin
    : respects_relation (MkMorph loop_c_eq)
        (fun x => Z.to_nat (Uint63.to_Z n - Uint63.to_Z (fst x))) lt.
  Proof.
    intros [i s] p; cbn -[Uint63.to_Z] in *; revert p; unfold loop_c_.
    destruct (i <? n)%uint63 eqn:E; intros p; [cbn -[Uint63.to_Z]; lia|].
    destruct (loop_done_empty p).
  Qed.

  Definition loop_c : RCoalg LoopF (int * St) := mk_wf_coalg wf_lt loop_c_fin.

  Definition loop : int * St ~> St := hylo loop_alg loop_c.

  Lemma loop_unfold i s
    : loop (i, s)
      =e if (i <? n)%uint63 then loop ((i + 1)%uint63, body i s) else s.
  Proof.
    unfold loop; rewrite (hylo_unr loop_alg loop_c (i, s)); cbn -[hylo];
      destruct (i <? n)%uint63; reflexivity.
  Qed.
End LoopDef.
Arguments LoopF St {eS}.
Arguments loop_step_valid St {eS}.

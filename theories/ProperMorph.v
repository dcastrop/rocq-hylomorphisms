Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Equivalence.
Require Import Hylo.Morphism.
Require Import Hylo.Container.
Require Import Hylo.Coalgebra.
Require Import Hylo.FCoalgebra.

From Stdlib Require Extraction.

(** Any named function [f] can be used where a morphism is expected, provided
  * [Proper (eqRel ==> eqRel) f] is found by typeclass resolution: this
  * default canonical structure is found by reversing the [app] coercion.
  * Anonymous functions are not found this way; use [morph_of] for them. *)
Definition proper_morph `{eA : setoid A} `{eB : setoid B} (f : A -> B)
  `{Hf : !Proper (eqRel ==> eqRel) f} : A ~> B := MkMorph Hf.
Arguments proper_morph {A eA B eB} f {Hf}.
Canonical Structure proper_morph.
Extraction Inline proper_morph.

(** Termination of a coalgebra, as a typeclass. *)
Class Terminates `{F : Cont Sh P} `{eA : setoid A} (c : Coalg F A) : Prop :=
  terminates : RecP c.

(** A named function [c] can be used where an [RCoalg] is expected, provided
  * [Terminates c] is found by typeclass resolution. Without this default,
  * Rocq would unfold [c] looking for a canonical [RCoalg] and not
  * terminate. *)
Canonical Structure proper_rcoalg `{F : Cont Sh P} `{eA : setoid A}
  (c : A -> App F A) `{Hc : !Proper (eqRel ==> eqRel) c}
  `{T : !Terminates (proper_morph c)} : RCoalg F A :=
  Rec (coalg := proper_morph c) T.
Extraction Inline proper_rcoalg.

#[export] Hint Unfold f_out f_nat_eta proper_rcoalg : canonical.

Ltac arewrite_unwrap ::=
  cbv [reverse_coercion]; autounfold with canonical; cbn [coalg natT].

(** * Finding [Proper] instances automatically *)

(** Functions on pairs of types whose equivalence is [=]. *)
#[export] Instance proper_pair_def_eq {A B} `{eC : setoid C} (f : A * B -> C)
  : Proper (@eqRel (A * B) (@pair_eq A (def_eq A) B (def_eq B)) ==> eqRel) f.
Proof. intros [a b] [c d] [E1 E2]; simpl in *; subst; reflexivity. Qed.

(** Functions out of [App F X], when the shapes of [F] are compared with [=]:
  * destruct the shape and anything the function matches on, then close the
  * goal by congruence, using the equivalence of the two continuations. *)
Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

(* Unfold the constant at the head of the left-hand side of the goal. *)
Ltac unfold_head :=
  lazymatch goal with
  | |- ?R ?l _ =>
      let h := head_of l in
      tryif is_const h then unfold h else idtac
  end.

Ltac proper_app :=
  let sx := fresh "sx" in let sy := fresh "sy" in
  let kx := fresh "kx" in let ky := fresh "ky" in
  let Es := fresh "Es" in let Ek := fresh "Ek" in
  intros [sx kx] [sy ky] [Es Ek]; simpl in Es, Ek; subst sy;
  try destruct sx; try unfold_head; simpl;
  repeat (match goal with
          | |- context [match ?s with _ => _ end] => is_var s; destruct s
          end; simpl in * );
  repeat first [ reflexivity
               | solve [apply Ek; auto]
               | progress (simpl; f_equal)
               | apply app_eq
               | constructor
               | let e1 := fresh "e1" in let e2 := fresh "e2" in
                 let Hv := fresh "Hv" in intros e1 e2 Hv; simpl in * ].

(* Instantiate the setoid instances of known types that are still evars in
   the goal: [proper_app] needs them to compute [eqRel]. *)
Ltac resolve_setoids :=
  repeat match goal with
         | |- context [@eqRel ?T ?s] =>
             is_evar s; tryif is_evar T then fail else
             let i := constr:(_ : setoid T) in unify s i
         end.

#[export] Hint Extern 10 (Proper (@eqRel (App _ _) _ ==> _) _) =>
  resolve_setoids; unfold Proper, respectful; solve [proper_app]
  : typeclass_instances.

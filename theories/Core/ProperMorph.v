Set Warnings "-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Core.Equivalence.
Require Import Hylo.Core.Morphism.
Require Import Hylo.Core.Container.
Require Import Hylo.Core.Coalgebra.
Require Import Hylo.Core.FCoalgebra.

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
#[mode = "- - - - - - -"]
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

#[export] Hint Unfold f_nat_eta proper_rcoalg : canonical.

Ltac arewrite_unwrap ::=
  cbv [reverse_coercion]; autounfold with canonical; cbn [coalg natT].

(** * Finding [Proper] instances automatically *)

(** Functions on pairs of types whose equivalence is [=]. *)
#[export] Instance proper_pair_def_eq {A B} `{eC : setoid C} (f : A * B -> C)
  : Proper (@eqRel (A * B) (@pair_eq A (def_eq A) B (def_eq B)) ==> eqRel) f.
Proof. intros [a b] [c d] [E1 E2]; simpl in *; subst; reflexivity. Qed.

(** Functions out of types whose equivalence implies [=]. *)
#[export] Instance proper_leibniz `{Leibniz A} `{eB : setoid B} (f : A -> B)
  : Proper (eqRel ==> eqRel) f | 0.
Proof. intros x y E; apply leibniz in E; subst; reflexivity. Qed.

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

(* Prove a goal [x =e y] by [x = y], when [=e] implies [=]. *)
Ltac leibniz_goal :=
  lazymatch goal with
  | |- @eq _ _ _ => fail
  | |- _ ?x ?y => change (x =e y); apply eq_leibniz
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
               | solve [apply leibniz, Ek; auto]
               | leibniz_goal
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

(** Functions out of polynomial types (pairs, sums, containers) with any
  * equivalences: decompose both arguments and their equivalence, replace the
  * components whose equivalence implies [=], and close the goal by
  * congruence with the component equivalences. *)
Ltac decompose_eq x y E :=
  let T := type of x in let T := eval hnf in T in
  lazymatch T with
  | prod _ _ =>
      let x1 := fresh "x" in let x2 := fresh "x" in
      let y1 := fresh "y" in let y2 := fresh "y" in
      let E1 := fresh "E" in let E2 := fresh "E" in
      destruct x as [x1 x2], y as [y1 y2], E as [E1 E2]; simpl in E1, E2;
      decompose_eq x1 y1 E1; decompose_eq x2 y2 E2
  | sum _ _ =>
      let x1 := fresh "x" in let y1 := fresh "y" in
      destruct x as [x1|x1], y as [y1|y1]; simpl in E; try contradiction;
      decompose_eq x1 y1 E
  | App _ _ =>
      let sx := fresh "sx" in let sy := fresh "sy" in
      let kx := fresh "kx" in let ky := fresh "ky" in
      let Es := fresh "Es" in let Ek := fresh "Ek" in
      destruct x as [sx kx], y as [sy ky], E as [Es Ek]; simpl in Es, Ek;
      decompose_eq sx sy Es
  | _ => first [subst y | apply leibniz in E; subst y | idtac]
  end.

Ltac proper_step :=
  first [ reflexivity
        | assumption
        | progress intros
        | match goal with
          | |- context [match ?s with _ => _ end] => is_var s; destruct s
          end
        | match goal with |- context [if ?c then _ else _] => destruct c end
        | solve [apply leibniz; assumption]
        | progress (simpl; f_equal)
        | apply app_eq
        | constructor
        | let v1 := fresh "v" in let V1 := fresh "V" in
          let v2 := fresh "v" in let V2 := fresh "V" in
          let Hv := fresh "Hv" in
          intros [v1 V1] [v2 V2] Hv; simpl in *
        | match goal with
          | Ek : forall _ _, val _ = val _ -> _ |- _ => apply Ek
          end ].

(* At most [n] steps on each goal, so that the search always terminates *)
Ltac proper_steps n :=
  lazymatch n with
  | O => idtac
  | S ?m => try (progress proper_step; proper_steps m)
  end.

Ltac proper_poly :=
  let x := fresh "x" in let y := fresh "y" in let E := fresh "E" in
  intros x y E; decompose_eq x y E; try unfold_head; simpl; proper_steps 100.

#[export] Hint Extern 11 (Proper (@eqRel (prod _ _) _ ==> _) _) =>
  resolve_setoids; unfold Proper, respectful; solve [proper_poly]
  : typeclass_instances.
#[export] Hint Extern 11 (Proper (@eqRel (sum _ _) _ ==> _) _) =>
  resolve_setoids; unfold Proper, respectful; solve [proper_poly]
  : typeclass_instances.
#[export] Hint Extern 11 (Proper (@eqRel (App _ _) _ ==> _) _) =>
  resolve_setoids; unfold Proper, respectful; solve [proper_poly]
  : typeclass_instances.

(** [Program Definition f : A ~> B := morphism g.] makes [g] a morphism,
  * proving it proper with [proper_poly]. If that fails (or takes more than 5
  * seconds), the proof is left as an obligation ([Next Obligation]). Other
  * obligations get the default tactic. *)
Notation "'morphism' f" := (@MkMorph _ _ _ _ f%function _)
  (at level 10, f at level 200).
#[export] Obligation Tactic :=
  first [solve [timeout 5 proper_poly] | Tactics.program_simpl].

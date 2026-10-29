Set Warnings "-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Core.Equivalence.
Require Import Hylo.Core.Morphism.
Require Import Hylo.Core.ProperMorph.

From elpi Require Import elpi.
From elpi.apps Require Import coercion.

(** * Curried functions as morphisms, automatically

  * Two ways of inserting [proper_morphn] (see [Hylo.Core.ProperMorph]), both
  * requiring [Proper (eqRel ==> ... ==> eqRel) f]:

  * 1. Named functions (and their partial applications), at any arity, are
  *    accepted where a morphism is expected, by a coercion: with
  *    [bset : B -> I -> A -> B], [flip bset : I ~> B ~> A ~> B].
  * 2. Anonymous functions, at any arity, need [morph_ofn]:
  *    [morph_ofn (fun b i a => bset b i a) : B ~> I ~> A ~> B].

  * Limitations:
  * - A bare [fun ...] is never coerced: Rocq rejects a [fun] whose expected
  *   type is not a product before trying any coercion. Use [morph_ofn].
  * - [morph_ofn] needs the expected type to be known when it is elaborated,
  *   unless the binders are typed. Under [flip], [comp], ..., whose argument
  *   types are still unknown, write [morph_ofn (fun (b : B) (i : I) ... => ...)].
  *   For the same reason, [morph_ofn f] for a named [f] fails there if [f]
  *   has implicit arguments (instance search runs inside the tactic and
  *   picks defaults for them); use the bare [f], which the coercion handles.
  * - Only non-dependent arrows: [forall x : A, B x] is not coerced.
  * - [Proper] is not derived for anonymous functions: a [fun] that is not an
  *   eta-expansion of a function with a [Proper] instance needs one. *)

(* The coercion runs only on type errors that the built-in coercions cannot
   fix. The morphism type is computed from the type of [F], which has all its
   arrows even when the expected type is only partly known; instance search is
   postponed ([@no-tc!]) until the whole term is elaborated, so that implicit
   arguments of [F] are fixed by then. *)
Elpi Accumulate coercion.db lp:{{
pred morph-of-fun i:term, o:term.
morph-of-fun (prod _ A (x\ B)) {{ lp:A ~> lp:M }} :- !, morph-of-fun B M.
morph-of-fun T T.

coercion _ F (prod _ _ _ as FTy) ({{ @morph _ _ _ _ }} as Expected) R :-
  morph-of-fun FTy M,
  @no-tc! => coq.elaborate-skeleton {{ @proper_morphn _ _ lp:M _ _ lp:F _ }}
               Expected R ok.
}}.

(* [morph_ofn F] receives [F] unelaborated, elaborates it against the plain
   function type of the expected morphism type (which gives the binders their
   types), and returns [proper_morphn F]. *)
Elpi Tactic morph_ofn.
Elpi Accumulate lp:{{
% The function type of a morphism type, as far as it is known.
pred fun-of-morph i:term, o:term.
fun-of-morph T {{ _ }} :- var T, !.
fun-of-morph {{ @morph lp:A _ lp:M _ }} (prod `x` A (_\ T)) :- !,
  fun-of-morph M T.
fun-of-morph T T.

solve (goal _ _ Ty Sol [trm F]) [] :-
  fun-of-morph Ty FT,
  (@no-tc! => coq.elaborate-ty-skeleton FT _ FT1 ok),
  (@no-tc! => coq.elaborate-skeleton F FT1 F1 ok),
  coq.elaborate-skeleton {{ @proper_morphn _ _ _ _ _ lp:F1 _ }} Ty R ok,
  Sol = R.
}}.
Elpi Query lp:{{
  coq.notation.add-abbreviation-for-tactic "morph_ofn" "morph_ofn" []
}}.

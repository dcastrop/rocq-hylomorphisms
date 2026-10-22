Set Warnings "-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Core.Utils.
Require Import Hylo.Core.Equivalence.
Require Import Hylo.Core.Morphism.
Require Import Hylo.Core.Container.

From Stdlib Require Import List.

#[mode = "- - - -"]
Class Finite `{Esh : setoid Sh} {P} (F : Cont Sh P) :=
  { members : forall s, list (Pos F s);
    members_proper : forall s1 s2,
      s1 =e s2 -> map val (members s1) = map val (members s2);
    members_complete : forall s (p : Pos F s), In p (members s);
    members_nodup : forall s, NoDup (members s);
  }.

Arguments members {Sh Esh P} F {_}.
Arguments members_proper {_ _ _} F {_} _ _ _.
Arguments members_complete {Sh Esh P} F {_} [s] p.
Arguments members_nodup {Sh Esh P} F {_} s.
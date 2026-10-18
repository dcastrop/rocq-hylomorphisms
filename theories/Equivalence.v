Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

From Stdlib Require Import Eqdep_dec.
From Stdlib Require Export Setoid.

Module BoolEq <: DecidableType.
  Definition U := bool.
  Lemma eq_dec (b1 b2 : U) : {b1 = b2} + {b1 <> b2}.
  Proof. decide equality. Qed.
End BoolEq.
Module DecBool := DecidableEqDep(BoolEq).

Definition bool_irrelevance {b1 b2 : bool} (p1 p2 : b1 = b2) : p1 = p2 :=
  DecBool.UIP b1 b2 p1 p2.

Reserved Notation "f =e g" (at level 70, no associativity).
(* Mode "!": no instance search on [setoid ?A] for an unknown [?A]. Instances
   such as [equiv_rcoalg] match any evar and recurse on a fresh one, so such a
   search never ends and exhausts memory. *)
#[mode = "!"]
Class setoid A : Type :=
  MkSetoid
    { eqRel : A -> A -> Prop;
      e_refl : forall x, eqRel x x;
      e_sym : forall x y, eqRel x y -> eqRel y x;
      e_trans : forall x y z, eqRel x y -> eqRel y z -> eqRel x z;
    }.

Notation "f =e g" := (eqRel f g).

Add Parametric Relation `{eq : setoid A} : A (@eqRel A eq)
    reflexivity proved by (@e_refl A eq)
    symmetry proved by (@e_sym A eq)
    transitivity proved by (@e_trans A eq)
      as ExtEq.

Create HintDb ffix.

#[export] Hint Resolve e_refl : ffix.
#[export] Hint Resolve e_sym : ffix.
#[export] Hint Resolve e_trans : ffix.

(** Prove [x =e y] by [x = y]: then [f_equal] and [reflexivity] apply. *)
Lemma eq_eqRel `{setoid A} (x y : A) : x = y -> x =e y.
Proof. intros ->; reflexivity. Qed.

Ltac to_eq :=
  lazymatch goal with |- ?R ?x ?y => change (x =e y); apply eq_eqRel end.

Definition def_eq A : setoid A :=
{| eqRel := @eq A;
  e_refl := @eq_refl A;
  e_sym := @eq_sym A;
  e_trans := @eq_trans A;
|}.

(** [=] is the fallback equivalence, for types that have no instance of their
  * own. It is never offered for an unknown type, nor for a type marked with
  * [NoDefEq] (declared next to each type's own [setoid] instance): otherwise
  * typeclass backtracking can pick [=] where the specific instance was
  * meant. *)
Class NoDefEq (A : Type) : Prop := {}.

Ltac def_eq_fallback A :=
  tryif is_evar A then fail else
  tryif assert_succeeds (let x := constr:(_ : NoDefEq A) in idtac) then fail
  else exact (def_eq A).

#[export] Hint Extern 100 (setoid ?A) => def_eq_fallback A
  : typeclass_instances.

#[export] Instance ext_eq (A : Type) `{eq_B : setoid B} : setoid (A -> B).
Proof.
  apply (@MkSetoid _ (fun f g => forall x, f x =e g x)); eauto with ffix.
Defined.

#[export] Instance pair_eq `{eq_A : setoid A} `{eq_B : setoid B}
  : setoid (A * B).
Proof.
  apply (@MkSetoid _ (fun x y => fst x =e fst y /\ snd x =e snd y));
    [| intros x y [->->] | intros x y z [->->]]; eauto with ffix.
Defined.

Add Parametric Morphism `{eA : setoid A} `{eB : setoid B}
  : (@Datatypes.pair A B)
    with signature
    (eqRel (A:=A))
      ==> (eqRel (A:=B))
      ==> (eqRel (A:=A * B))
      as coqPairMorphism.
Proof. split; trivial. Qed.

#[export] Instance sum_eq `{eq_A : setoid A} `{eq_B : setoid B}
  : setoid (A + B).
Proof.
  apply (@MkSetoid _ (fun x y => match x, y with
                                 | inl u, inl v | inr u, inr v => u =e v
                                 | _, _ => False
                                 end));
    [intros [] | intros [] [] | intros [] [] []]; eauto with ffix;
    contradiction.
Defined.

#[export] Instance prop_eq : setoid Prop :=
  {| eqRel := iff; e_refl := iff_refl; e_sym := @iff_sym;
     e_trans := @iff_trans |}.

#[export] Instance pred_sub `{eA : setoid A} {P : A -> Prop}
  : setoid {a : A | P a}.
Proof.
  apply (@MkSetoid _ (fun px py => proj1_sig px =e proj1_sig py));
    eauto with ffix.
Defined.

Fixpoint list_eqR `{setoid A} (x y : list A) : Prop :=
  match x, y with
  | nil, nil => True
  | a :: x, b :: y => a =e b /\ list_eqR x y
  | _, _ => False
  end%list.

Ltac destruct_list_match :=
  match goal with
  | |- context [match ?l with nil => _ | cons _ _ => _ end] => is_var l; destruct l
  | H : context [match ?l with nil => _ | cons _ _ => _ end] |- _ => is_var l; destruct l
  end.

#[local] Hint Extern 4 =>
  progress (simpl in *); intuition (eauto with ffix) : ffix.
#[local] Hint Extern 5 =>
  destruct_list_match; simpl in *; intuition (eauto with ffix) : ffix.

#[export] Program Instance list_eq `{eA : setoid A} : setoid (list A)
  := { eqRel := list_eqR }.
Solve All Obligations with (induction x; eauto with ffix).

#[export] Hint Extern 1 (list_eqR ?x ?y) => change (x =e y) : ffix.

Add Parametric Relation `{eA : setoid A} : (list A) (@list_eqR A eA)
    reflexivity proved by (@e_refl (list A) list_eq)
    symmetry proved by (@e_sym (list A) list_eq)
    transitivity proved by (@e_trans (list A) list_eq)
      as ListEq.

(** Types whose equivalence implies [=]. *)
#[mode = "! -"]
Class Leibniz T `{setoid T} : Prop := leibniz : forall x y : T, x =e y -> x = y.
Arguments Leibniz T {_}.

Lemma eq_leibniz `{Leibniz T} (x y : T) : x = y -> x =e y.
Proof. intros ->; reflexivity. Qed.

Lemma def_eq_leibniz T : @Leibniz T (def_eq T).
Proof. intros x y E; exact E. Qed.

(* As for [def_eq_fallback]: only for types without a setoid of their own. *)
#[export] Hint Extern 100 (@Leibniz ?T _) =>
  tryif assert_succeeds (let x := constr:(_ : NoDefEq T) in idtac) then fail
  else exact (@def_eq_leibniz T) : typeclass_instances.

#[export] Instance pair_leibniz `{Leibniz A} `{Leibniz B} : Leibniz (A * B).
Proof. intros [] [] []; f_equal; apply leibniz; trivial. Qed.

#[export] Instance list_leibniz `{Leibniz A} : Leibniz (list A).
Proof.
  intros x; induction x; intros [] E; simpl in *; try contradiction; trivial.
  destruct E; f_equal; auto.
Qed.

#[export] Instance ext_no_def_eq A B : NoDefEq (A -> B) := {}.
#[export] Instance pair_no_def_eq A B : NoDefEq (A * B) := {}.
#[export] Instance sum_no_def_eq A B : NoDefEq (A + B) := {}.
#[export] Instance prop_no_def_eq : NoDefEq Prop := {}.
#[export] Instance sig_no_def_eq A (P : A -> Prop)
  : NoDefEq {a : A | P a} := {}.
#[export] Instance list_no_def_eq A : NoDefEq (list A) := {}.

#[mode = "-"]
Class equivs (A : list Type) : Prop.
#[export] Instance e_nil : equivs (@nil Type) := {}.
#[export] Instance e_cons `{setoid A} `{equivs B} : equivs (A :: B) := {}.

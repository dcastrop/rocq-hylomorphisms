Set Warnings "-bad-template-constraint,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Core.
Require Import Hylo.Schemes.Hylomorphisms.

(** * Hylomorphisms with CPS coalgebras

  * A CPS version of a recursive coalgebra [c] passes its layer to a
  * continuation, inside its own case analysis, together with the proof that
  * the layer is [c x]. [hylo_cps] applies the algebra in that continuation,
  * so the algebra meets a known layer. [hylo_cps_hylo] rewrites it into
  * [hylo]. *)
Section CPSDef.
  Context `{F : Cont Sh P} `{eA : setoid A} `{eB : setoid B}.
  Context (c : RCoalg F A).

  Local Unset Implicit Arguments.
  Record CCoalg := MkCCoalg {
    ccoalg : forall (R : Type) (x : A), (forall y, y = c x -> R) -> R;
    ccoalg_law : forall (R : Type) (x : A) (k : forall y, y = c x -> R),
      ccoalg R x k = k (c x) eq_refl
  }.
  Local Set Implicit Arguments.

  (* The children of [y] terminate, if [y] is [c x] and [x] terminates *)
  Definition RecF_inv_eq x y (E : y = c x) (H : RecF c x)
    : forall e, RecF c (cont y e) :=
    match H in RecF _ x0 return y = c x0 -> forall e, RecF c (cont y e) with
    | RecF_fold h => fun E =>
        match eq_sym E in _ = z return forall e, RecF c (cont z e) with
        | eq_refl => h
        end
    end E.

  Context (a : Alg F B) (cc : CCoalg).

  Definition hylo_cps_def : forall x, RecF c x -> B :=
    fix f x H :=
      ccoalg cc B x (fun y E =>
        a (MkCont (shape y) (fun e => f (cont y e) (RecF_inv_eq E H e)))).

  Lemma hylo_cps_def_hylo
    : forall x (H : RecF c x), hylo_cps_def H =e hylo a c x.
  Proof.
    fix Ih 2; intros ? [x h].
    etransitivity; [|symmetry; apply (hylo_unr a c x)].
    cbn [hylo_cps_def]; rewrite ccoalg_law; cbn [RecF_inv_eq eq_sym].
    apply (app_eq a); split; [reflexivity|]; intros e1 e2 Ev; cbn.
    rewrite Ih, (elem_val_eq Ev); reflexivity.
  Qed.

  Lemma hylo_cps_eq : forall x y, x =e y ->
    hylo_cps_def (terminating c x) =e hylo_cps_def (terminating c y).
  Proof. intros x y E; rewrite !hylo_cps_def_hylo, E; reflexivity. Qed.

  Definition hylo_cps : A ~> B := MkMorph hylo_cps_eq.

  Theorem hylo_cps_hylo : hylo_cps =e hylo a c.
  Proof. intros x; apply hylo_cps_def_hylo. Qed.
End CPSDef.

(** * Building CPS coalgebras

  * [cps_from_coalg] builds a [CCoalg c] from the case analyses of [c]: each
  * [match e] in [c x] becomes [convoy e], whose branches know the equation
  * [Hq : pattern = e], and each layer [L] is passed as [k L E], with [E]
  * proved by rewriting with those equations. [cps_law] proves the law. *)
Definition convoy {S R : Type} (s : S) (M : forall q, q = s -> R) : R :=
  M s eq_refl.
Arguments convoy {S R} s M.

Lemma convoy_law {S R : Type} (s : S) (M : forall q, q = s -> R) (h : R)
  : (forall q E, M q E = h) -> convoy s M = h.
Proof. intros H; apply H. Qed.

Lemma cps_irrel {Y R : Type} (z : Y) (k : forall y, y = z -> R) y (E : y = z)
  : k y E = k z eq_refl.
Proof. destruct E; reflexivity. Qed.

Ltac cps_law :=
  intros; cbv beta;
  repeat (apply convoy_law;
          let q := fresh "q" in let E := fresh "E" in
          intros q E; destruct q; cbv beta iota);
  apply cps_irrel.

(* [L = c x], rewriting the scrutinees of [c x] by the branch equations *)
Ltac cps_eq :=
  repeat (lazymatch goal with |- ?l = ?r =>
            let r' := eval hnf in r in change (l = r') end;
          lazymatch goal with
          | H : _ = ?e |- _ = match ?e with _ => _ end => rewrite <- H; clear H
          end);
  reflexivity.

Ltac cps_build k L :=
  lazymatch L with
  | match ?e with _ => _ end =>
      let F := lazymatch eval pattern e in L with ?F _ => F end in
      let q := fresh "q" in let H := fresh "Hq" in
      refine (convoy e (fun q H => _)); destruct q;
      lazymatch type of H with ?p = _ =>
        let L' := eval hnf in (F p) in cps_build k L'
      end
  | _ => refine (k L _); cps_eq
  end.

Ltac cps_from_coalg :=
  lazymatch goal with |- CCoalg ?c =>
    simple refine {| ccoalg := _; ccoalg_law := _ |};
    [ let R := fresh "R" in let x := fresh "x" in let k := fresh "k" in
      intros R x k; let L := eval hnf in (c x) in cps_build k L
    | cps_law ]
  end.

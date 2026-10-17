Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Equivalence.

From Stdlib Require Export Morphisms.

Reserved Notation "x ~> y" (at level 95, right associativity, y at level 200).

Section Defn.
  Context `{eA : setoid A} `{eB : setoid B}.

  (* TODO: use canonical structures, handle inlining when extracting code *)
  Structure morph :=
    MkMorph
      { app :> A -> B;
        app_eq : forall x y, x =e y -> app x =e app y
      }.
  Hint Resolve app_eq : ffix.

  #[export] Instance eq_morph : setoid morph.
  Proof.
    apply (@MkSetoid _ (fun f g => forall x, app f x =e app g x));
      eauto with ffix.
  Defined.
  #[export] Instance morph_no_def_eq : NoDefEq morph := {}.
End Defn.
Arguments morph A {eA} B {eB}.
Notation "x ~> y" := (morph x y).
#[export] Hint Resolve app_eq : ffix.

(** [morph_of f] is the morphism of a function [f] whose properness,
  * [Proper (eqRel ==> eqRel) f], is found by typeclass resolution. It is a
  * notation, so it leaves nothing behind in extracted code. *)
Abbreviation morph_of f :=
  (@MkMorph _ _ _ _ f%function
     (_ : Proper (eqRel ==> eqRel)%signature f%function)).

(** Functions out of a type whose equivalence is [=] are always proper. *)
#[export] Instance proper_def_eq {A} `{eB : setoid B} (f : A -> B)
  : Proper (@eqRel A (def_eq A) ==> eqRel) f.
Proof. intros x y ->. reflexivity. Qed.

Lemma f_equal `{setoid A} `{setoid B} (f g : A ~> B)
  : forall x, f =e g -> f x =e g x.
Proof. intros x E. apply E. Qed.

Add Parametric Morphism `{eA : setoid A} `{eB : setoid B}
  : (@app A eA B eB)
    with signature
    (eqRel (A:=A~>B))
      ==> (eqRel (A:=A))
      ==> (eqRel (A:=B))
      as appMorphism.
Proof. intros ?? Efg x y Exy; rewrite (Efg x); apply app_eq, Exy. Qed.

Add Parametric Morphism `{eA : setoid A} `{eB : setoid B}
  : (@app A eA B eB)
    with signature
    (eqRel (A:=A~>B))
      ==> (eqRel (A:=A->B))
      as appMorphism2.
Proof. intros ?? E; apply E. Qed.

Section Id.
  Context `{eA : setoid A}.

  Abbreviation id_ := (fun x => x).

  Lemma id_eq : forall x y : A, x =e y -> id_ x =e id_ y.
  Proof. auto. Qed.

  Definition id : A ~> A := {| app := _; app_eq := id_eq |}.
End Id.

Section Const.
  Context `{eA : setoid A} `{eB : setoid B}.
  Abbreviation const_ := (fun (k : B) (_ : A) => k).

  Lemma const_eq1 (k : B)
    : forall x y : A, x =e y -> (const_ k) x =e (const_ k) y.
  Proof. auto with ffix. Qed.
  Definition const1 (k : B) : A ~> B
    := {| app := _; app_eq := const_eq1 k |}.

  Lemma const_eq : forall x y : B, x =e y -> const1 x =e const1 y.
  Proof. intros ????. trivial. Qed.

  Definition const : B ~> A ~> B := {| app := _; app_eq := const_eq |}.
End Const.

Section Exp.
  Context `{setoid A} `{setoid B} `{setoid C}.

  Abbreviation eapp_ := (fun x : (_ ~> _) * _ => let (f, v) := x in f v).

  Lemma eapp_eq : forall x y : (A ~> B) * A, x =e y -> eapp_ x =e eapp_ y.
  Proof. intros [][][E1 E2]; simpl in *; rewrite (app_eq m E2); apply E1. Qed.

  Definition eapp := MkMorph eapp_eq.

  Abbreviation papp_ f := (fun x y => f y x).
  Lemma papp_eq (f : A ~> B ~> C) (v : B)
    : forall x y : A, x =e y -> papp_ f v x =e papp_ f v y.
  Proof. intros ?? E. simpl. apply (f_equal v), app_eq, E. Qed.
  Definition papp f v := MkMorph (papp_eq f v).

  Lemma flip_eq1 (f : A ~> B ~> C)
    : forall x y : B, x =e y -> papp f x =e papp f y.
  Proof. intros x y E a; exact (app_eq (f a) E). Qed.
  Abbreviation flip1 := (fun f => MkMorph (flip_eq1 f)).

  Lemma flip_eq : forall f g : A ~> B ~> C, f =e g -> flip1 f =e flip1 g.
  Proof. intros f g E b a; exact (E a b). Qed.
  Definition flip : (A ~> B ~> C) ~> B ~> A ~> C := MkMorph flip_eq.
End Exp.

Reserved Notation "f \o g" (at level 50, format "f  \o '/ '  g").
Section Comp.
  Context `{setoid A} `{setoid B} `{setoid C}.
  Abbreviation comp_ := (fun f g => (fun x => f (g x))).

  Lemma comp_eq2 (g : B ~> C) (f : A ~> B)
    : forall x y, x =e y -> (comp_ g f) x =e (comp_ g f) y.
  Proof. intros; apply app_eq, app_eq; trivial. Qed.
  Abbreviation comp2 := (fun g f => MkMorph (comp_eq2 g f)).

  Lemma comp_eq1 (g : B ~> C)
    : forall x y : A ~> B, x =e y -> (comp2 g) x =e (comp2 g) y.
  Proof. intros ?? E ?. simpl. apply app_eq, E. Qed.
  Abbreviation comp1 := (fun g => MkMorph (comp_eq1 g)).

  Lemma comp_eq : forall x y : B ~> C, x =e y -> comp1 x =e comp1 y.
  Proof. intros ?? E ??. apply E. Qed.
  Definition comp : (B ~> C) ~> (A ~> B) ~> A ~> C := MkMorph comp_eq.
End Comp.
Notation "f \o g" := (comp f g).

Lemma compA `{setoid A} `{setoid B} `{setoid C} `{setoid D}
  (f : C ~> D) (g : B ~> C) (h : A ~> B) : f \o (g \o h) =e (f \o g) \o h.
Proof. intros x; reflexivity. Qed.
Lemma idKl `{setoid A} `{setoid B} (f : A ~> B) : id \o f =e f.
Proof. intros x; reflexivity. Qed.
Lemma idKr `{setoid A} `{setoid B} (f : A ~> B) : f \o id =e f.
Proof. intros x; reflexivity. Qed.

(** * Rewriting modulo associativity of [\o]
  *
  * Chains of compositions are kept right-associated, like lists. [arewrite H]
  * (with [H : l =e r]) scans the chain on each side of the goal for the first
  * position where the elements of [l] unify, one by one, with consecutive
  * elements, and replaces them by [r]: a proof by conversion, with no setoid
  * rewriting. If [l] does not occur at the top level of the goal, plain
  * [rewrite] is tried, using [H] also as [forall k, l \o k =e r \o k].
  *
  * No step rewrites with [compA]: reassociation is syntactic, and justified by
  * conversion ([=e] on morphisms is pointwise, and compositions compute).
  * Unification tolerates terms that are only convertible, where [rewrite]
  * (which matches syntactically) fails. As a last resort, the goal's
  * canonical-structure wrappers ([reverse_coercion], and the structures
  * registered with [Hint Unfold c : canonical]) are unfolded and both steps
  * retried: they hide compositions, and make equal morphisms differ
  * syntactically. Chains nested
  * inside other terms (e.g. an algebra passed to [hylo]) are only reached by
  * the plain [rewrite].
  *
  * Patterns spell out [app]/[comp]: [\o] in a pattern does not match, its
  * implicit setoids being unresolved. *)
Ltac reassoc t :=
  lazymatch t with
  | @app _ _ _ _
      (@app _ _ _ _ (@comp _ _ _ _ _ _)
         (@app _ _ _ _ (@app _ _ _ _ (@comp _ _ _ _ _ _) ?f) ?g)) ?h =>
      reassoc (f \o (g \o h))
  | @app _ _ _ _ (@app _ _ _ _ (@comp _ _ _ _ _ _) ?f) ?g =>
      let g' := reassoc g in constr:(f \o g')
  | _ => t
  end.

(* The right-associated chain [c] followed by [k]. *)
Ltac append c k :=
  lazymatch c with
  | @app _ _ _ _ (@app _ _ _ _ (@comp _ _ _ _ _ _) ?f) ?g =>
      let g' := append g k in constr:(f \o g')
  | _ => constr:(c \o k)
  end.

(* Prove a pointwise instance of [H] by computing the compositions. *)
Ltac by_conv H :=
  let x := fresh "x" in
  intros x; generalize (H x); cbn [app comp]; exact (fun P => P).

Ltac assoc_r :=
  lazymatch goal with
  | |- @eqRel ?T ?e ?l ?r =>
      let l' := reassoc l in let r' := reassoc r in
      let P := fresh in
      enough (P : @eqRel T e l' r') by by_conv P
  end.

(* If the chain [s] begins with the elements of the chain [l], compared by
   unification, call [k] with what follows them in [s], or with [tt] if
   nothing does. *)
Ltac seg_rest l s k :=
  lazymatch l with
  | @app _ _ _ _ (@app _ _ _ _ (@comp _ _ _ _ _ _) ?l1) ?lt =>
      lazymatch s with
      | @app _ _ _ _ (@app _ _ _ _ (@comp _ _ _ _ _ _) ?s1) ?st =>
          unify l1 s1; seg_rest lt st k
      end
  | _ =>
      first [ lazymatch s with
              | @app _ _ _ _ (@app _ _ _ _ (@comp _ _ _ _ _ _) ?s1) ?st =>
                  unify l s1; k st
              end
            | unify l s; k tt ]
  end.

(* The first position in the chain [c] where [l] begins, scanning left to
   right; [pre] is the chain before [c], or [tt]. Calls [k pre rest]. *)
Ltac find_seg l c pre k :=
  first [ seg_rest l c ltac:(fun rest => k pre rest)
        | lazymatch c with
          | @app _ _ _ _ (@app _ _ _ _ (@comp _ _ _ _ _ _) ?a) ?t =>
              let pre' := lazymatch pre with tt => a | _ => append pre a end in
              find_seg l t pre' k
          end ].

(* [pre \o (l \o rest)] is replaced by [pre \o (r \o rest)]; [E x] relates
   the two pointwise. *)
Ltac seg_new r pre rest :=
  let r' := reassoc r in
  let s := lazymatch rest with tt => r' | _ => append r' rest end in
  lazymatch pre with tt => s | _ => append pre s end.

Ltac seg_eq H pre rest x :=
  let Hx :=
    lazymatch rest with tt => constr:(H x) | _ => constr:(H (rest x)) end in
  lazymatch pre with tt => Hx | _ => constr:(app_eq pre Hx) end.

Ltac seg_rewrite H l r :=
  lazymatch goal with
  | |- @eqRel ?T ?e ?L ?R =>
      let Hn := fresh in let x := fresh "x" in
      first
        [ find_seg l L tt ltac:(fun pre rest =>
            let N := seg_new r pre rest in
            enough (Hn : @eqRel T e N R) by
              (intros x; let E := seg_eq H pre rest x in
               generalize E (Hn x); cbn [app comp];
               let E1 := fresh in let E2 := fresh in
               intros E1 E2; exact (e_trans E1 E2)))
        | find_seg l R tt ltac:(fun pre rest =>
            let N := seg_new r pre rest in
            enough (Hn : @eqRel T e L N) by
              (intros x; let E := seg_eq H pre rest x in
               generalize E (Hn x); cbn [app comp];
               let E1 := fresh in let E2 := fresh in
               intros E1 E2; exact (e_trans E2 (e_sym E1)))) ]
  end.

(* The first element of the chain [c] that unifies with [e]; calls [k pre suf],
   where [suf] is the suffix of [c] starting with that element. *)
Ltac find_elem e c pre k :=
  first [ lazymatch c with
          | @app _ _ _ _ (@app _ _ _ _ (@comp _ _ _ _ _ _) ?a) _ =>
              unify e a; k pre c
          | _ => unify e c; k pre c
          end
        | lazymatch c with
          | @app _ _ _ _ (@app _ _ _ _ (@comp _ _ _ _ _ _) ?a) ?t =>
              let pre' := lazymatch pre with tt => a | _ => append pre a end in
              find_elem e t pre' k
          end ].

(** [ainsert H before e], with [H : l =e id], inserts the chain [l] before the
  * first element of a chain in the goal that unifies with [e]. *)
Ltac ainsert_ H e :=
  lazymatch type of H with
  | @eqRel _ _ ?l _ =>
      assoc_r;
      lazymatch goal with
      | |- @eqRel ?T ?ee ?L ?R =>
          let Hn := fresh in let x := fresh "x" in
          first
            [ find_elem e L tt ltac:(fun pre suf =>
                let N := seg_new l pre suf in
                enough (Hn : @eqRel T ee N R) by
                  (intros x; let E := seg_eq H pre suf x in
                   generalize E (Hn x); cbn [app comp id];
                   let E1 := fresh in let E2 := fresh in
                   intros E1 E2; exact (e_trans (e_sym E1) E2)))
            | find_elem e R tt ltac:(fun pre suf =>
                let N := seg_new l pre suf in
                enough (Hn : @eqRel T ee L N) by
                  (intros x; let E := seg_eq H pre suf x in
                   generalize E (Hn x); cbn [app comp id];
                   let E1 := fresh in let E2 := fresh in
                   intros E1 E2; exact (e_trans E2 E1))) ]
      end
  end.
Tactic Notation "ainsert" constr(H) "before" constr(e) := ainsert_ H e.

(* Unfold canonical-structure wrappers that hide compositions or make equal
   morphisms differ syntactically. Canonical structures are registered with
   [Hint Unfold c : canonical]; [ProperMorph] adds the reduction of the
   structures' projections. *)
Create HintDb canonical discriminated.
Ltac arewrite_unwrap := cbv [reverse_coercion]; autounfold with canonical.

Ltac arewrite_ H :=
  lazymatch type of H with
  | @eqRel (@morph ?A ?eA ?B ?eB) ?e ?l ?r =>
      let l' := reassoc l in let r' := reassoc r in
      let H0 := fresh "H" in let Hk := fresh "Hk" in
      assert (H0 : @eqRel (@morph A eA B eB) e l' r') by by_conv H;
      assert (Hk : forall (X : Type) (eX : setoid X) (k : @morph X eX A eA),
                 ltac:(let lk := append l' k in let rk := append r' k in
                       exact (lk =e rk)))
        by (intros ? ? k; by_conv (fun x => H (k x)));
      assoc_r;
      first [ seg_rewrite H l' r' | rewrite Hk | rewrite H0
            | arewrite_unwrap; assoc_r;
              first [seg_rewrite H l' r' | rewrite Hk | rewrite H0] ];
      clear H0 Hk; assoc_r
  end.

Tactic Notation "arewrite" constr(H) := arewrite_ H.
Tactic Notation "arewrite" "<-" constr(H) := arewrite_ (e_sym H).

Section Pairs.
  Context `{eA : setoid A} `{eB : setoid B} `{eC : setoid C}.
  Abbreviation fst_ := (fun x : _ * _ => let (y, _) := x in y).
  Abbreviation snd_ := (fun x : _ * _ => let (_, y) := x in y).
  Lemma fst_eq :
    forall x y : A * B, x =e y -> fst_ x =e fst_ y.
  Proof. intros [][][]; trivial. Qed.
  Lemma snd_eq :
    forall x y : A * B, x =e y -> snd_ x =e snd_ y.
  Proof. intros [][][]; trivial. Qed.
  Definition fst : A * B ~> A := MkMorph fst_eq.
  Definition snd : A * B ~> B := MkMorph snd_eq.

  Abbreviation pair_ f g := (fun x => (f x, g x)).

  Lemma pair_feq2 (f : A ~> B) (g : A ~> C) :
    forall x y : A, x =e y -> (pair_ f g) x =e (pair_ f g) y.
  Proof. intros; split; apply app_eq; trivial. Qed.

  Abbreviation pair2 := (fun f g => MkMorph (pair_feq2 f g)).

  Lemma pair_feq1 (f : A ~> B)
    : forall x y : A ~> C, x =e y -> (pair2 f) x =e (pair2 f) y.
  Proof. intros ?? E ?. split; [reflexivity|apply E]. Qed.
  Abbreviation pair1 := (fun f => MkMorph (pair_feq1 f)).

  Lemma pair_feq
    : forall x y : A ~> B, x =e y -> pair1 x =e pair1 y.
  Proof. intros ?? E ?. split; [apply E|reflexivity]. Qed.
  Definition pair := MkMorph pair_feq.
End Pairs.

Lemma fst_pair `{setoid A} `{setoid B} `{setoid C} (f : A ~> B) (g : A ~> C) :
  fst \o pair f g =e f.
Proof. intros x; reflexivity. Qed.
Lemma snd_pair `{setoid A} `{setoid B} `{setoid C} (f : A ~> B) (g : A ~> C) :
  snd \o pair f g =e g.
Proof. intros x; reflexivity. Qed.

Lemma pair_fusion
  `{setoid A} `{setoid B1} `{setoid B2} `{setoid C1} `{setoid C2}
  (h : A ~> B1) (i : A ~> B2) (f : B1 ~> C1) (g : B2 ~> C2)
  : pair (f \o fst) (g \o snd) \o pair h i =e pair (f \o h) (g \o i).
Proof. intros x. split; reflexivity. Qed.

Section Sums.
  Context `{setoid A} `{setoid B} `{setoid C}.
  Lemma inj1_eq : forall x y : A, x =e y -> inl x =e (inl y : A + C).
  Proof. auto. Qed.
  Lemma inj2_eq : forall x y : A, x =e y -> inr x =e (inr y : C + A).
  Proof. auto. Qed.
  Definition inj1 : A ~> A + C := MkMorph inj1_eq.
  Definition inj2 : A ~> C + A := MkMorph inj2_eq.

  Abbreviation fcase_ f g
    := (fun x => match x with | inl y => f y | inr y => g y end).

  Lemma fcase_eq2 (f : A ~> C) (g : B ~> C) :
    forall x y : A + B, x =e y -> (fcase_ f g) x =e (fcase_ f g) y.
  Proof. intros [][]; simpl; try intros[]; apply app_eq; trivial. Qed.
  Abbreviation fcase2 := (fun f g => MkMorph (fcase_eq2 f g)).

  Lemma fcase_eq1 (f : A ~> C) :
    forall x y : B ~> C, x =e y -> (fcase2 f) x =e (fcase2 f) y.
  Proof. intros ?? E []; simpl; try reflexivity; try apply E. Qed.
  Abbreviation fcase1 := (fun f => MkMorph (fcase_eq1 f)).

  Lemma fcase_eq : forall x y : A ~> C, x =e y -> fcase1 x =e fcase1 y.
  Proof. intros ?? E [][]; simpl; try reflexivity; try apply E. Qed.
  Definition fcase := MkMorph fcase_eq.
End Sums.

Lemma inj1_case `{setoid A} `{setoid B} `{setoid C} (f : A ~> C) (g : B ~> C) :
  fcase f g \o inj1 =e f.
Proof. intros x; reflexivity. Qed.
Lemma inj2_case `{setoid A} `{setoid B} `{setoid C} (f : A ~> C) (g : B ~> C) :
  fcase f g \o inj2 =e g.
Proof. intros x; reflexivity. Qed.

Lemma eapp_pair_const `{setoid A} `{setoid B} `{setoid C}
  (f : B ~> C) (g : A ~> B) : eapp \o pair (const f) g =e f \o g.
Proof. intros x; reflexivity. Qed.

Lemma eapp_pair_id `{setoid A} `{setoid B} `{setoid C} (f : A ~> B ~> C) :
  eapp \o pair (const f) id =e f.
Proof. intros x; reflexivity. Qed.

Definition uncurry `{setoid A} `{setoid B} `{setoid C} (f : A ~> B ~> C)
    : A * B ~> C := eapp \o pair (f \o fst) snd.

Definition curry `{setoid A} `{setoid B} `{setoid C} (f : A * B ~> C)
  : A ~> B ~> C := comp f \o papp pair id \o const.

Section SpecDef.
  Context `{eA : setoid A} `{eB : setoid B}.
  Record Ext (f : A ~> B) :=
    MkExt
      { target :> A -> B;
        tgt_eq : app f =e target;
      }.
End SpecDef.

Ltac calculate := eapply MkExt.

Section PredSubty.
  Context `{eA : setoid A} `{eB : setoid B}.

  Definition liftP_f_ (f : A ~> B) (P : B -> Prop) (Pf : forall x, P (f x))
    : A -> {x : B | P x}
    := (fun x => exist (fun fx => _) (f x) (Pf x)).

  Lemma liftP_f_arr (P : B -> Prop) (f : A ~> B) (Pf : forall x, P (f x))
    : forall x y, x =e y -> liftP_f_ Pf x =e liftP_f_ Pf y.
  Proof. simpl; auto with ffix. Qed.

  Definition liftP (f : A ~> B) (P : B -> Prop) (Pf : forall x, P (f x))
    : A ~> {x : B | P x}
    := MkMorph (liftP_f_arr Pf).
End PredSubty.

Arguments liftP {A}%_type_scope {eA} {B}%_type_scope {eB} f {P}
  Pf%_function_scope.

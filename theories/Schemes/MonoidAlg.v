Set Warnings "-bad-template-constraint,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.

Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Core.
Require Import Hylo.Schemes.Hylomorphisms.

From Stdlib Require Import List.

(** Monoid algebras: algebras that fold a monoid over the children of a
  * finite container. *)

(** * Monoids *)

Record Monoid `{eW : setoid W} :=
  MkMonoid
    { skip : W;
      par : W ~> W ~> W;
      par_assoc : forall a b c, par a (par b c) =e par (par a b) c;
      par_skip_l : forall a, par skip a =e a;
      par_skip_r : forall a, par a skip =e a;
    }.
Arguments Monoid W {_}.

(** * Notation

  * [a <+> b] and [<0>] use the only monoid on the carrier in the context; they
  * fail if there are several, and then [a <+>[ M ] b] and [<0>[ M ]] name it.
  * [MonoidOf] is never the type of a hypothesis, so its only instances come
  * from [unique_monoid]. A concrete monoid is opened with
  * [#[local] Hint Extern 0 (@MonoidOf T _) => exact M
  *    : typeclass_instances]. *)

#[mode = "! -"]
Class MonoidOf W `{setoid W} := monoid_of : Monoid W.
Arguments MonoidOf W {_}.

Ltac unique_monoid W :=
  match goal with
  | M1 : @Monoid W _, M2 : @Monoid W _ |- _ =>
      tryif constr_eq M1 M2 then fail else fail 1
  | M : @Monoid W _ |- _ => exact M
  end.
#[export] Hint Extern 0 (@MonoidOf ?W _) => unique_monoid W
  : typeclass_instances.

Notation "a <+>[ M ] b" := (par M a b)
  (at level 50, M at level 0, left associativity, only parsing).
Notation "<0>[ M ]" := (skip M) (M at level 0, only parsing).
Notation "a <+> b" := (par (_ : MonoidOf _) a b)
  (at level 50, left associativity, only parsing).
Notation "a <+> b" := (par _ a b)
  (at level 50, left associativity, only printing).
Notation "<0>" := (skip (_ : MonoidOf _)) (only parsing).
Notation "<0>" := (skip _) (only printing).

Record MonoidHom `{eW : setoid W} `{eV : setoid V}
  (M : Monoid W) (N : Monoid V) (h : W ~> V) : Prop :=
  { hom_skip : h <0>[M] =e <0>[N];
    hom_par : forall a b, h (a <+>[M] b) =e h a <+>[N] h b;
  }.

(** * Semirings: [mul] distributes over [add] on the left, and [add]'s unit
  * absorbs on the right. *)
Record Semiring `{eW : setoid W} :=
  MkSemiring
    { sadd : Monoid W;
      smul : Monoid W;
      sdistr : forall x a b,
        x <+>[smul] (a <+>[sadd] b)
        =e (x <+>[smul] a) <+>[sadd] (x <+>[smul] b);
      sabsorb : forall x, x <+>[smul] <0>[sadd] =e <0>[sadd];
    }.
Arguments Semiring W {_}.

Lemma smul_hom `{setoid W} (S : Semiring W) (x : W)
  : MonoidHom (sadd S) (sadd S) (par (smul S) x).
Proof. split; [apply sabsorb | apply sdistr]. Qed.

Section MConcat.
  Context `(M : @Monoid W eW).

  (** Fold a list with [par], adding no units: [mconcat [x] = x]. *)
  Fixpoint mconcat (l : list W) : W :=
    match l with
    | nil => <0>
    | x :: l' =>
        match l' with
        | nil => x
        | _ :: _ => x <+> mconcat l'
        end
    end.

  Lemma mconcat_proper (l1 l2 : list W)
    : Forall2 eqRel l1 l2 -> mconcat l1 =e mconcat l2.
  Proof.
    induction 1 as [|x1 x2 l1 l2 Ex El Ih]; simpl; [reflexivity|].
    destruct El; trivial; rewrite Ex, Ih; reflexivity.
  Qed.
End MConcat.

Lemma mconcat_hom `{eW : setoid W} `{eV : setoid V}
  (M : Monoid W) (N : Monoid V) (h : W ~> V) (Hh : MonoidHom M N h)
  (l : list W)
  : h (mconcat M l) =e mconcat N (map h l).
Proof.
  induction l as [|x [|y l] Ih]; simpl; [apply hom_skip, Hh | reflexivity |].
  rewrite (hom_par Hh), Ih; reflexivity.
Qed.

Section ListMonoid.
  Context `{setoid A}.
  Program Definition list_monoid : Monoid (list A) :=
    {| skip := nil; par := lapp |}.
  Solve All Obligations with
    (intros; simpl; rewrite ?app_assoc, ?app_nil_r; eauto with ffix).
End ListMonoid.

Section OMap.
  Context `{eA : setoid A} `{eB : setoid B}.

  Definition omap_ (f : A ~> B) (x : option A) : option B :=
    match x with
    | None => None
    | Some a => Some (f a)
    end.

  Lemma omap_morph (f : A ~> B)
    : forall x y, x =e y -> omap_ f x =e omap_ f y.
  Proof. intros [x|] [y|]; simpl; auto with ffix. Qed.

  Definition omap (f : A ~> B) : option A ~> option B :=
    MkMorph (omap_morph f).

  #[export] Instance omap_proper : Proper (eqRel ==> eqRel) omap.
  Proof. intros f g E [x|]; simpl; auto. Qed.
End OMap.

Lemma omap_comp `{setoid A} `{setoid B} `{setoid C} (g : B ~> C) (f : A ~> B)
  : omap g \o omap f =e omap (g \o f).
Proof. intros [x|]; simpl; reflexivity. Qed.

Definition opt_cons {A} (o : option A) (l : list A) : list A :=
  match o with
  | None => l
  | Some x => x :: l
  end.

Lemma opt_cons_proper `{setoid A} (o1 o2 : option A) (l1 l2 : list A)
  : o1 =e o2 -> Forall2 eqRel l1 l2 ->
    Forall2 eqRel (opt_cons o1 l1) (opt_cons o2 l2).
Proof. destruct o1, o2; simpl; try intros []; auto. Qed.

Lemma Forall2_eqRel_refl `{setoid A} (l : list A) : Forall2 eqRel l l.
Proof. induction l; constructor; auto with ffix. Qed.

Lemma map_opt_cons {A B} (f : A -> B) (o : option A) (l : list A)
  : map f (opt_cons o l) = opt_cons (option_map f o) (map f l).
Proof. destruct o; reflexivity. Qed.

(** * Monoid algebras *)

Section MAlg.
  Context `{@Finite Sh Esh P F} `{setoid W} (M : Monoid W).

  Lemma map_cont_rel (s1 s2 : Sh) (k1 : Pos F s1 -> W) (k2 : Pos F s2 -> W)
    (Ek : forall e1 e2, val e1 = val e2 -> k1 e1 =e k2 e2)
    : forall (l1 : list (Pos F s1)) (l2 : list (Pos F s2)),
      map val l1 = map val l2 -> Forall2 eqRel (map k1 l1) (map k2 l2).
  Proof.
    induction l1 as [|e1 l1 Ih]; intros [|e2 l2]; simpl; try discriminate;
      [auto|]; intros E; injection E as Ev El; constructor; auto.
  Qed.

  (** A node folds its own value [leaf s], if any, and its children, in the
    * order of [members]. *)
  Definition malg_ (leaf : Sh ~> option W) (x : App F W) : W :=
    let (s, k) := x in mconcat M (opt_cons (leaf s) (map k (members F s))).

  Lemma malg_morph (leaf : Sh ~> option W)
    : forall x y, x =e y -> malg_ leaf x =e malg_ leaf y.
  Proof.
    intros [sx kx] [sy ky] [Es Ek]; simpl in *.
    apply mconcat_proper, opt_cons_proper;
      [apply app_eq | apply (map_cont_rel Ek), members_proper]; exact Es.
  Qed.

  Definition malg (leaf : Sh ~> option W) : Alg F W :=
    MkMorph (malg_morph leaf).
End MAlg.

Arguments malg {_}%_type_scope {_} {_}%_type_scope F {_} {_}%_type_scope {_}
  _ _.

#[export] Instance malg_proper `{@Finite Sh Esh P F} `(M : @Monoid W eW)
  : Proper (eqRel ==> eqRel) (malg F M).
Proof.
  intros l1 l2 E [s k]; simpl.
  apply mconcat_proper, opt_cons_proper; [apply E | apply Forall2_eqRel_refl].
Qed.

(** * Fusion with monoid homomorphisms *)
Section Fusion.
  Context `{@Finite Sh Esh P F} `(M : @Monoid W eW) `(N : @Monoid V eV)
    `(Hh : MonoidHom M N h).

  Lemma malg_hom (leaf : Sh ~> option W)
    : h \o malg F M leaf =e malg F N (omap h \o leaf) \o fmap h.
  Proof.
    intros [s k]; simpl; rewrite (mconcat_hom Hh); apply mconcat_proper.
    rewrite map_opt_cons, map_map; destruct (leaf s); apply Forall2_eqRel_refl.
  Qed.

  Lemma malg_fusion `{eA : setoid A} (leaf : Sh ~> option W)
    (c : RCoalg F A)
    : h \o hylo (malg F M leaf) c =e hylo (malg F N (omap h \o leaf)) c.
  Proof. apply hylo_fusion_l, malg_hom. Qed.
End Fusion.

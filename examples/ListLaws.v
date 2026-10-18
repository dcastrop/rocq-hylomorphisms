Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

From Hylo Require Import Hylo.
Require Import Hylo.Utils.
Require Import Hylo.FiniteCont.
Require Import Hylo.MonoidAlg.

Require Import Hylo.Examples.CList.

From Stdlib Require Import List.

Section Reduce.
  Context `{Leibniz A} `{setoid W} (M : Monoid W).

  Definition cons_leaf (w : A ~> W) : Lshape A ~> option W :=
    morph_of (fun s => match s with s_nil => None | s_cons a => Some (w a) end).

  Definition reduce (w : A ~> W) : list A ~> W :=
    hylo (malg (ListF A) M (cons_leaf w)) ilist_coalg.

  Lemma reduce_nil (w : A ~> W) : reduce w nil =e <0>.
  Proof. unfold reduce; rewrite hylo_unr; reflexivity. Qed.

  Lemma reduce_cons (w : A ~> W) a l : reduce w (a :: l) =e w a <+> reduce w l.
  Proof. unfold reduce; rewrite hylo_unr at 1; reflexivity. Qed.
End Reduce.
Arguments reduce : simpl never.

Section ReduceLaws.
  Context `{Leibniz A} `{setoid W} (M : Monoid W).

  #[export] Instance reduce_proper : Proper (eqRel ==> eqRel) (reduce (A:=A) M).
  Proof.
    intros w1 w2 E l; induction l as [|a l Ih];
      rewrite ?reduce_nil, ?reduce_cons; [reflexivity|].
    rewrite (E a), Ih; reflexivity.
  Qed.

  Lemma reduce_app (w : A ~> W) l1 l2
    : reduce M w (l1 ++ l2) =e reduce M w l1 <+> reduce M w l2.
  Proof.
    induction l1 as [|a l1 Ih]; simpl app.
    - rewrite reduce_nil, par_skip_l; reflexivity.
    - rewrite !reduce_cons, Ih, par_assoc; reflexivity.
  Qed.

  Lemma reduce_hom (w : A ~> W) : MonoidHom list_monoid M (reduce M w).
  Proof. split; [apply reduce_nil | intros a b; apply reduce_app]. Qed.
End ReduceLaws.

Section ReduceFusion.
  Context `{Leibniz A} `{setoid W} `{setoid V} (M : Monoid W) (N : Monoid V)
    `(Hh : MonoidHom M N h).

  Lemma reduce_fusion (w : A ~> W) : h \o reduce M w =e reduce N (h \o w).
  Proof.
    intros l; cbn [Morphism.app comp]; induction l as [|a l Ih];
      rewrite ?reduce_nil, ?reduce_cons.
    - apply hom_skip, Hh.
    - rewrite (hom_par Hh), Ih; reflexivity.
  Qed.
End ReduceFusion.

Definition sing `{Leibniz B} : B ~> list B := morph_of (fun b => b :: nil).

Definition lmap `{Leibniz A} `{Leibniz B} (f : A ~> B) : list A ~> list B :=
  reduce list_monoid (sing \o f).
Arguments lmap : simpl never.

Definition concat `{Leibniz A} : list (list A) ~> list A := reduce list_monoid id.

Lemma reduce_sing `{Leibniz A} `{setoid W} (M : Monoid W) (w : A ~> W)
  : reduce M w \o sing =e w.
Proof. intros a; cbn [Morphism.app comp sing]; rewrite reduce_cons, reduce_nil, par_skip_r; reflexivity. Qed.

Section Promotion.
  Context `{Leibniz A} `{Leibniz W} (M : Monoid W).

  Lemma promotion (h : list A ~> W) (Hh : MonoidHom list_monoid M h)
    : h \o concat =e reduce M id \o lmap h.
  Proof.
    unfold concat, lmap; rewrite (reduce_fusion Hh), (reduce_fusion (reduce_hom M id)).
    apply reduce_proper; intros x; cbn [Morphism.app comp sing].
    rewrite reduce_cons, reduce_nil, par_skip_r; reflexivity.
  Qed.
End Promotion.

Lemma reduce_promotion `{Leibniz W} (M : Monoid W)
  : reduce M id \o concat =e reduce M id \o lmap (reduce M id).
Proof. apply promotion, reduce_hom. Qed.

Lemma map_promotion `{Leibniz A} `{Leibniz B} (f : A ~> B)
  : lmap f \o concat =e concat \o lmap (lmap f).
Proof. apply promotion, reduce_hom. Qed.

Lemma reduce_lmap `{Leibniz A} `{Leibniz B} `{setoid W} (M : Monoid W)
  (w : B ~> W) (f : A ~> B)
  : reduce M w \o lmap f =e reduce M (w \o f).
Proof.
  unfold lmap; rewrite (reduce_fusion (reduce_hom M w)).
  apply reduce_proper; intros x; cbn [Morphism.app comp sing].
  rewrite reduce_cons, reduce_nil, par_skip_r; reflexivity.
Qed.

Lemma lmap_comp `{Leibniz A} `{Leibniz B} `{Leibniz C} (f : B ~> C) (g : A ~> B)
  : lmap f \o lmap g =e lmap (f \o g).
Proof.
  unfold lmap at 1; rewrite reduce_lmap.
  apply reduce_proper; intros x; reflexivity.
Qed.

#[export] Instance lmap_proper `{Leibniz A} `{Leibniz B}
  : Proper (eqRel ==> eqRel) (@lmap A _ _ B _ _).
Proof.
  intros f g E; apply reduce_proper; intros x; cbn [Morphism.app comp sing].
  rewrite (leibniz (E x)); reflexivity.
Qed.

Lemma lmap_nil `{Leibniz A} `{Leibniz B} (f : A ~> B) : lmap f nil = nil.
Proof. apply leibniz, reduce_nil. Qed.

Lemma lmap_cons `{Leibniz A} `{Leibniz B} (f : A ~> B) a l
  : lmap f (a :: l) = f a :: lmap f l.
Proof. apply leibniz; unfold lmap; rewrite reduce_cons; reflexivity. Qed.

Lemma reduce_lmap_app `{Leibniz A} `{Leibniz B} `{setoid W} (M : Monoid W)
  (w : B ~> W) (f : A ~> B) l
  : reduce M w (lmap f l) =e reduce M (w \o f) l.
Proof. apply (reduce_lmap M w f l). Qed.

Lemma reduce_map `{Leibniz A} `{Leibniz B} `{setoid W} (M : Monoid W)
  (w : B ~> W) (f : A ~> B) l
  : reduce M w (map f l) =e reduce M (w \o f) l.
Proof.
  induction l as [|a l Ih]; simpl map; rewrite ?reduce_nil, ?reduce_cons;
    [reflexivity|]; rewrite Ih; reflexivity.
Qed.

Section Folds.
  Context `{Leibniz A}.

  Definition foldr_alg `{setoid B} (f : A ~> B ~> B) (e : B)
    : App (ListF A) B ~> B :=
    morph_of (fun x : App (ListF A) B =>
      match x with
      | MkCont s k =>
          match s as s return (Container.Pos (ListF A) s -> B) -> B with
          | s_nil => fun _ => e
          | s_cons a => fun k => f a (k (MkElem tt (p_cons eq_refl)))
          end k
      end).

  Definition foldr `{setoid B} (f : A ~> B ~> B) (e : B) : list A ~> B :=
    hylo (foldr_alg f e) ilist_coalg.

  Definition scan_alg `{Leibniz B} (f : A ~> B ~> B) (e : B)
    : App (ListF A) (list B) ~> list B :=
    morph_of (fun x : App (ListF A) (list B) =>
      match x with
      | MkCont s k =>
          match s as s return (Container.Pos (ListF A) s -> list B) -> list B with
          | s_nil => fun _ => e :: nil
          | s_cons a => fun k =>
              let zs := k (MkElem tt (p_cons eq_refl)) in f a (hd e zs) :: zs
          end k
      end).

  Definition scanr `{Leibniz B} (f : A ~> B ~> B) (e : B) : list A ~> list B :=
    hylo (scan_alg f e) ilist_coalg.

  Definition tails_alg : App (ListF A) (list (list A)) ~> list (list A) :=
    morph_of (fun x : App (ListF A) (list (list A)) =>
      match x with
      | MkCont s k =>
          match s as s return (Container.Pos (ListF A) s -> _) -> _ with
          | s_nil => fun _ => nil :: nil
          | s_cons a => fun k =>
              let yss := k (MkElem tt (p_cons eq_refl)) in (a :: hd nil yss) :: yss
          end k
      end).

  Definition tails : list A ~> list (list A) := hylo tails_alg ilist_coalg.

  Definition cons_m (a : A) : list A ~> list A := morph_of (cons a).

  Definition inits_alg : App (ListF A) (list (list A)) ~> list (list A) :=
    morph_of (fun x : App (ListF A) (list (list A)) =>
      match x with
      | MkCont s k =>
          match s as s return (Container.Pos (ListF A) s -> _) -> _ with
          | s_nil => fun _ => nil :: nil
          | s_cons a => fun k => nil :: map (cons_m a) (k (MkElem tt (p_cons eq_refl)))
          end k
      end).

  Definition inits : list A ~> list (list A) := hylo inits_alg ilist_coalg.
End Folds.

Lemma foldr_nil `{Leibniz A} `{setoid B} (f : A ~> B ~> B) e : foldr f e nil =e e.
Proof. unfold foldr; rewrite hylo_unr; reflexivity. Qed.

Lemma foldr_cons `{Leibniz A} `{setoid B} (f : A ~> B ~> B) e a l
  : foldr f e (a :: l) =e f a (foldr f e l).
Proof. unfold foldr; rewrite hylo_unr at 1; reflexivity. Qed.

Section FoldLaws.
  Context `{Leibniz A}.

  Lemma scan_lemma `{Leibniz B} (f : A ~> B ~> B) (e : B)
    : lmap (foldr f e) \o tails =e scanr f e.
  Proof.
    unfold tails, scanr; apply hylo_fusion_l; intros [[|a] k];
      apply eq_leibniz; cbn -[lmap foldr reduce].
    - rewrite lmap_cons, lmap_nil, (leibniz (foldr_nil f e)); reflexivity.
    - rewrite !lmap_cons, (leibniz (foldr_cons f e _ _)).
      destruct (k _) as [|ys yss]; cbn -[lmap foldr reduce];
        rewrite ?lmap_nil, ?lmap_cons, ?(leibniz (foldr_nil f e)); reflexivity.
  Qed.

  Lemma foldr_lmap `{Leibniz B} `{setoid C} (f : B ~> C ~> C) (g : A ~> B) e
    : foldr f e \o lmap g =e foldr (f \o g) e.
  Proof.
    unfold foldr at 2; apply hylo_uniq; intros [|a l]; cbn -[lmap foldr reduce].
    - rewrite lmap_nil, foldr_nil; reflexivity.
    - rewrite lmap_cons, foldr_cons; reflexivity.
  Qed.
End FoldLaws.

Section Horner.
  Context `{Leibniz W} (S : Semiring W).

  Definition horner_step : W ~> W ~> W :=
    comp (par (sadd S) (skip (smul S))) \o par (smul S).

  Lemma horner
    : reduce (sadd S) id \o lmap (reduce (smul S) id) \o inits
      =e foldr horner_step (skip (smul S)).
  Proof.
    rewrite reduce_lmap; unfold inits, foldr; apply hylo_fusion_l.
    intros [[|a] k]; cbn -[lmap foldr reduce].
    - rewrite reduce_cons, reduce_nil, par_skip_r; cbn -[reduce]; rewrite reduce_nil; reflexivity.
    - rewrite reduce_cons, reduce_map.
      assert (E : reduce (sadd S) ((id \o reduce (smul S) id) \o cons_m a)
                  =e reduce (sadd S) (par (smul S) a \o (id \o reduce (smul S) id)))
        by (apply reduce_proper; intros ys; cbn -[reduce]; rewrite reduce_cons; reflexivity).
      rewrite E.
      rewrite <- (reduce_fusion (smul_hom S a)); cbn -[reduce]; rewrite reduce_nil; reflexivity.
  Qed.
End Horner.

Section Tupling.
  Context `{Leibniz A} `{Leibniz B} (M : Monoid B).

  Definition hd_m (e : B) : list B ~> B := morph_of (hd e).

  Definition tup (g : B -> B) (p : B * B) : B * B :=
    let z := g (Datatypes.snd p) in (z <+> Datatypes.fst p, z).
  Arguments tup : simpl never.

  Definition tup_step (f : A ~> B ~> B) : A ~> B * B ~> B * B :=
    morph_of (fun a => morph_of (tup (f a))).

  Lemma scan_tupling (f : A ~> B ~> B) (e : B)
    : reduce M id \o scanr f e =e fst \o foldr (tup_step f) (e, e).
  Proof.
    assert (E : pair (reduce M id) (hd_m e) \o scanr f e =e foldr (tup_step f) (e, e)).
    { unfold scanr, foldr; apply hylo_fusion_l; intros [[|a] k];
        cbn -[reduce]; unfold tup; cbn -[reduce]; split;
        rewrite ?reduce_cons, ?reduce_nil, ?par_skip_r; reflexivity. }
    rewrite <- E; intros l; reflexivity.
  Qed.
End Tupling.

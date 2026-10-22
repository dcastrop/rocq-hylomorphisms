Set Warnings "-bad-template-constraint,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import Hylo.Hylo.

From Stdlib Require List.

(* Defining a tree *)
Unset Auto Template Polymorphism.

Inductive ITreeF L N X := leaf (ELEM : L) | node (ELEM : N) (LB RB : X).
Arguments leaf & {L N X} ELEM.
Arguments node & {L N X} ELEM LB RB.

(* shapes *)
Inductive Ts L A := | Leaf (ELEM : L) | Node (ELEM : A).
Inductive Tp := | Lbranch | Rbranch. (* positions *)
(* position valid in shape? *)

Definition t_dom {L A} (x : Ts L A * Tp) : bool :=
  match x with
  | (Node _ _, _)  => true
  | _            => false
  end.
#[local]
  Instance TreeF (L A : Type) : Cont (Ts L A) Tp :=
  { valid := @t_dom L A }.
Definition Tree L A := LFix (TreeF L A).

(* A named morphism, not a plain function: it is the key of the canonical
   [naturalM] structure [nt_tree] below. *)
Definition nt_shape {L L' A A'} (f : L ~> L') (g : A ~> A')
  : Ts L A ~> Ts L' A' :=
  morph_of (fun x => match x with
                     | Leaf _ l => Leaf _ (f l)
                     | Node _ n => Node _ (g n)
                     end).

Lemma nt_shape_is_nat {L L' A A'} (f : L ~> L') (g : A ~> A')
  : NaturalIn (TreeF L A) (TreeF L' A') (nt_shape f g).
Proof. intros [l|n] p; trivial. Qed.

Canonical Structure nt_tree {L L' A A'} (f : L ~> L') (g : A ~> A')
  : naturalM (TreeF L A) (TreeF L' A')
  := {| natT := nt_shape f g; natC := @nt_shape_is_nat _ _ _ _ f g |}.
#[export] Hint Unfold nt_tree : canonical.

Definition map_tree {L L' A A'} (f : L ~> L') (g : A ~> A')
  : LFix (TreeF L A) ~> LFix (TreeF L' A') :=
  everywhere (nt_shape f g).

Lemma dom_leaf_false L A (x : L) : Pos (TreeF L A) (Leaf A x) -> False.
Proof. intros []; simpl in *; discriminate. Qed.
Definition dom_leaf L A B (e : L) (x : Pos (TreeF L A) (Leaf A e)) : B :=
  False_rect _ (dom_leaf_false x).

Abbreviation a_leaf x := (MkCont (Leaf _ x) (@dom_leaf _ _ _ x)).
Abbreviation a_node x l r :=
  (MkCont (Node _ x) (fun p => match val p with
                              | Lbranch => l
                              | Rbranch => r
                              end)).

Definition lnode_valid {L A} (x : Ts L A)
  : forall (n : A), x = Node L n -> valid (x, Lbranch) = true.
Proof. intros n ->. reflexivity. Qed.
Definition rnode_valid {L A} (x : Ts L A)
  : forall (n : A), x = Node L n -> valid (x, Rbranch) = true.
Proof. intros n ->. reflexivity. Qed.

Abbreviation e_lbranch k H := (k (MkElem Lbranch (lnode_valid H))).
Abbreviation e_rbranch k H := (k (MkElem Rbranch (rnode_valid H))).
Abbreviation leftB  k := (e_lbranch k eq_refl).
Abbreviation rightB k := (e_rbranch k eq_refl).

Definition posL {A} (h : A) : Pos (TreeF unit A) (Node unit h) :=
  MkElem Lbranch eq_refl.
Definition posR {A} (h : A) : Pos (TreeF unit A) (Node unit h) :=
  MkElem Rbranch eq_refl.

Definition a_out {L A X : Type} (x : App (TreeF L A) X) : ITreeF L A X :=
  let (s, k) := x in
  match s as s' return s = s' -> ITreeF L A X with
  | Leaf _ x => fun _ => leaf x
  | Node _ n => fun E => node n (e_lbranch k E) (e_rbranch k E)
  end eq_refl.
Arguments a_out {L A X} x /.
#[export] Hint Unfold a_out posL posR : unfold_code.
#[export] Hint Unfold nt_tree nt_shape : unfold_code.

Inductive itree L A := | i_leaf (l : L) | i_node (x : A) (l r : itree L A).
Definition to_tree {L A} (x : itree L A) : App (TreeF L A) (itree L A) :=
  match x with
  | i_leaf _ l => a_leaf l
  | i_node n l r => a_node n l r
  end.

Lemma to_tree_rec {L A} : RecP (@to_tree L A).
Proof.
  intros x. induction x as [l|n l Ihl r Ihr]; constructor; simpl; intros e.
  - apply (dom_leaf _ e).
  - destruct (val e); trivial.
Defined.

Definition fto_tree {L A}: RCoalg (TreeF L A) (itree L A) := Rec to_tree_rec.

Definition itree_to_tree {L A} : itree L A ~> Tree L A :=
  rana fto_tree.

Definition to_itree {L A} : App (TreeF L A) (itree L A) ~> itree L A :=
  morph_of (fun x : App (TreeF L A) (itree L A) =>
    match a_out x with
    | leaf l => i_leaf _ l
    | node n l r => i_node n l r
    end).
Definition tree_to_itree {L A} : Tree L A ~> itree L A := cata to_itree.

Lemma tree_itree_iso1 {L A}
  : itree_to_tree (L:=L) (A:=A) \o tree_to_itree =e id.
Proof.
  Opaque to_tree_rec cata rana.
  intros x; unfold tree_to_itree, itree_to_tree.
  induction x as [[[|n] kx] Ih]; rewrite cata_unfold, rana_unfold; simpl in *;
    split; trivial.
  - intros e; apply (dom_leaf _ e).
  - intros [[|] V1] [v2 V2]; simpl; intros <-.
    + rewrite (bool_irrelevance V2 (lnode_valid eq_refl)); trivial.
    + rewrite (bool_irrelevance V2 (rnode_valid eq_refl)); trivial.
  Transparent to_tree_rec cata rana.
Qed.

(* For some reason [Tree] needs unfolding ... *)
Lemma tree_itree_iso2 {L A}
  : tree_to_itree \o itree_to_tree =e id (A:=itree L A).
Proof.
  unfold tree_to_itree, itree_to_tree, Tree; rewrite cata_ana_hylo.
  symmetry; rewrite hylo_uniq, fmap_id, idKr; intros []; simpl; trivial.
Qed.

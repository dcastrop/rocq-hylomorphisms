Set Warnings "-bad-template-constraint,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import Hylo.Core.
Require Import Hylo.Schemes.

From Stdlib Require List.

Unset Auto Template Polymorphism.

Inductive IListF H T := i_nil | i_cons (h : H) (t : T).
Arguments i_nil  & {H T}.
Arguments i_cons & {H T} h t.

(* shapes *)
Inductive Lshape H := | s_nil | s_cons (h : H).
Arguments s_nil & {H}.
Definition Lpos := unit. (* positions *)
(* position valid in shape? *)

Definition l_valid {H} (x : Lshape H * Lpos) : bool :=
  match x with
  | (s_cons _, _)  => true
  | _              => false
  end.

#[local]
Instance ListF (H : Type) : Cont (Lshape H) Lpos := { valid := @l_valid H }.

Definition List H := LFix (ListF H).

(* A named morphism, not a plain function: it is the key of the canonical
   [naturalM] structure [natural_list] below. *)
Definition l_map_shape {H H'} (f : H ~> H') : Lshape H ~> Lshape H' :=
  morph_of (fun x => match x with
                     | s_nil => s_nil
                     | s_cons h => s_cons (f h)
                     end).

Lemma map_shape_is_nt {H H'} (f : H ~> H')
  : NaturalIn (ListF H) (ListF H') (l_map_shape f).
Proof. intros [|n] p; trivial. Qed.

Canonical Structure natural_list {H H'} (f : H ~> H')
  : naturalM (ListF H) (ListF H')
  := {| natT := l_map_shape f; natC := @map_shape_is_nt _ _ f |}.
#[export] Hint Unfold natural_list : canonical.

Lemma dom_nil_false H : Pos (ListF H) (@s_nil H) -> False.
Proof. intros []; simpl in *; discriminate. Qed.
Lemma nil_uninhabited {H B} (x : Pos (ListF H) (@s_nil H)) : B x.
Proof. apply (False_rect _ (dom_nil_false x)). Defined.
Hint Extern 0 => (apply nil_uninhabited) : ffix.

Abbreviation a_nil := (MkCont (@s_nil _) (@nil_uninhabited _ _)).
Abbreviation a_cons h t := (MkCont (s_cons h) (fun _ => t)).

Local Definition a_in {H X : Type} (x : IListF H X) : App (ListF H) X :=
  match x with
  | i_nil => a_nil
  | i_cons h t => a_cons h t
  end.

Lemma p_cons {H s} {h : H} : s = s_cons h -> valid(s, tt).
Proof. intros ->; reflexivity. Qed.

Abbreviation get_tail k E := (k (MkElem tt (p_cons E))).

Definition l_members {H} (s : Lshape H) : list (Pos (ListF H) s) :=
  match s as s return list (Pos (ListF H) s) with
  | s_nil => nil
  | s_cons _ => MkElem tt (p_cons eq_refl) :: nil
  end.

#[export] Instance ListF_finite {H} : Finite (ListF H).
Proof.
  refine {| members := l_members |}.
  - intros s1 s2 ->; reflexivity.
  - intros [|h] [[] V]; simpl; [discriminate V |].
    left; f_equal; apply bool_irrelevance.
  - intros [|h]; repeat constructor; simpl; auto.
Defined.

Local Definition a_out {H X : Type} (x : App (ListF H) X) : IListF H X :=
  let (s, k) := x in
  match s as s' return s = s' -> IListF H X with
  | s_nil => fun E => i_nil
  | s_cons h => fun E => i_cons h (get_tail k E)
  end eq_refl.

Definition ilist_alg {A} : App (ListF A) (list A) ~> list A :=
  morph_of (fun x : App (ListF A) (list A) =>
    let (s, k) := x in
    match s as s' return s = s' -> list A with
    | s_nil => fun _ => nil
    | s_cons h => fun E => cons h (get_tail k E)
    end eq_refl).

Definition ilist_coalg {A} (x : list A) : App (ListF A) (list A) :=
  match x with
  | nil => a_nil
  | cons h t => a_cons h t
  end.
Arguments ilist_coalg {A} x /.
Lemma ilist_coalg_rec `{Leibniz A} : RecP (@ilist_coalg A).
Proof. intros x; induction x; constructor; auto with ffix. Defined.

#[export] Hint Unfold
  ilist_coalg ilist_alg ListF_finite l_members : unfold_code.
#[export] Hint Unfold natural_list l_map_shape : unfold_code.

#[export] Instance ilist_coalg_terminates `{Leibniz A}
  : Terminates (@ilist_coalg A) := ilist_coalg_rec.

Definition ilist_to_List {A} : list A ~> List A := rana ilist_coalg.
Definition List_to_ilist {A} : List A ~> list A := cata ilist_alg.

Lemma ilist_List_iso1 {A} : @ilist_to_List A \o List_to_ilist =e id.
Proof.
  unfold ilist_to_List, List_to_ilist, List; intros x.
  Opaque eqRel rana cata LFixR.
  induction x as [[[|h] kx] Ih];
    rewrite rana_unfold, cata_unfold; simpl in *; constructor; auto with ffix.
  - intros e1; destruct (dom_nil_false e1).
  - intros [[] V1] [[] V2] E; simpl in *.
    rewrite (bool_irrelevance V2 (p_cons (@eq_refl _ (s_cons h)))); apply Ih.
  Transparent eqRel rana cata LFixR.
Qed.

Lemma ilist_List_iso {A} : @List_to_ilist A \o ilist_to_List =e id.
Proof.
  unfold ilist_to_List, List_to_ilist, List.
  rewrite cata_ana_hylo; symmetry; apply hylo_uniq.
  rewrite fmap_id, idKr; intros [|h t]; auto with ffix.
Qed.

Definition Lmap {A B} (f : A ~> B) : List A ~> List B :=
  everywhere (natural_list f).

(* TODO: get rid of all of these with canonical structures *)
Definition ILmap {A B} (f : A ~> B) (x : list A) : list B := List.map f x.

Lemma ifmap_fmap {A B} (f : A ~> B) :
  ilist_coalg (A:=B) \o ILmap f
  =e natural (natural_list f) \o fmap (ILmap f) \o ilist_coalg.
Proof.
  intros []; simpl in *; auto with ffix; constructor; simpl; auto with ffix.
  intros e; destruct (dom_nil_false e).
Qed.

Lemma fmap_ifmap {A B} (f : A ~> B) :
  ILmap f \o ilist_alg (A:=A)
  =e ilist_alg \o natural (natural_list f) \o fmap (ILmap f).
Proof.
  intros [[|h] k]; simpl in *; auto with ffix.
  rewrite (bool_irrelevance (map_shape_is_nt _) (p_cons eq_refl));
    intuition (auto with ffix).
Qed.

Lemma list_map_nat {A B} (f : A ~> B) :
  Lmap f \o ilist_to_List =e ilist_to_List \o ILmap (app f).
Proof.
  unfold ilist_to_List, List, Lmap, everywhere.
  rewrite <- hylo_cata, cata_ana_hylo, hylo_ana; symmetry.
  apply hylo_uniq; rewrite hylo_unr at 1.
  arewrite (ifmap_fmap f).
  arewrite <- (natural_fmap (natural_list f) (hylo l_in (ilist_coalg (A:=B)))).
  rewrite fmap_comp; assoc_r; reflexivity.
Qed.

Lemma list_ww2 {A B} (f : A ~> B) :
  List_to_ilist \o Lmap f =e ILmap f \o List_to_ilist.
Proof.
  unfold List_to_ilist, Lmap, List, everywhere.
  rewrite hylo_map_shift, <- hylo_ana, cata_ana_hylo, hylo_cata; symmetry.
  apply hylo_uniq; rewrite fmap_comp.
  arewrite <- (natural_fmap (natural_list f) (hylo (@ilist_alg A) l_out)).
  arewrite <- (natural_fmap (natural_list f) (ILmap f)).
  arewrite <- (fmap_ifmap f); arewrite <- (hylo_unr (@ilist_alg A) l_out).
  reflexivity.
Qed.

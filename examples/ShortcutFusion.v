Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

From Hylo Require Import Hylo.
Require Import Hylo.Utils.

Require Import Hylo.Examples.BTree.
Require Import Hylo.Examples.CList.

From Stdlib Require Import List.
From Stdlib Require Import Uint63.

(** Example 1 from shortcut fusion in calc form:
  * [length \o map f \o append ys] *)
Definition tau_alg_ {A} `{setoid B} (l : list A) (a : Alg (ListF A) B)
  : App (ListF A) B -> B :=
  fun x =>
    match x with
    | MkCont sx kx =>
        match sx with
        | s_nil => fun _ => (hylo a ilist_coalg) l
        | s_cons h => fun kx => a (MkCont (s_cons h) kx)
        end kx
    end.

Lemma tau_alg_morph {A} `{setoid B} (l : list A) (a : Alg (ListF A) B) :
  forall x y, x =e y -> tau_alg_ l a x =e tau_alg_ l a y.
Proof.
  intros [sx kx] [sy ky] [Sxy Kxy]; simpl in *; subst.
  destruct sy as [|h]; simpl; [reflexivity|].
  apply app_eq; constructor; auto with ffix.
Qed.

Definition tau_alg {A} `{setoid B} (ys : list A) (a : Alg (ListF A) B)
  := Eval unfold tau_alg_ in MkMorph (tau_alg_morph ys a).

Lemma tau_fusion {A B} `{setoid C} `{setoid D} (ys : list A)
  (f : RCoalg (ListF A) D) (g : Alg (ListF A) D) (CANCEL : f \o g =e id)
  (a : Alg (ListF A) B) (c : RCoalg (ListF A) C):
  hylo (tau_alg ys a) c =e hylo a f \o hylo (tau_alg ys g) c.
Proof.
  symmetry; apply hylo_fusion_l.
  Opaque hylo.
  intros [[|h] kx].
  - simpl.
    replace (hylo a f (hylo g ilist_coalg ys)) with
      ((hylo a f \o hylo g ilist_coalg) ys) by reflexivity.
    rewrite (deforest CANCEL); reflexivity.
  - Opaque eqRel. simpl. rewrite hylo_unr at 1. simpl. apply app_eq.
    destruct (CANCEL {| shape := s_cons h; cont := kx|}) as [Sxy Kxy].
    simpl in *; constructor; auto with ffix.
    intros [v1 V1] [v2 V2] E; simpl in *; apply app_eq, Kxy; trivial.
    Transparent hylo eqRel.
Qed.

Definition append {A} (l : list A) := hylo (tau_alg l l_in) ilist_coalg.

Lemma tt_cons {A} (a : A) : valid (F:=ListF A)(s_cons a, tt).
Proof. reflexivity. Qed.
Definition len_alg {A} : App (ListF A) int ~> int :=
  morph_of (fun x : App (ListF A) int =>
    match x with
    | MkCont sx kx =>
        match sx as s return (Container.Pos (ListF A) s -> _) -> _ with
        | s_nil => fun _ => 0%uint63
        | s_cons _ => fun k => (1 + k (MkElem tt (@tt_cons _ _)))%uint63
        end kx
    end).

Definition length {A} := cata (@len_alg A).

Definition example1 {A B} (f : A ~> B) ys
  : Ext (length \o Lmap f \o append ys).
Proof.
  calculate.
  unfold length, Lmap, append, everywhere.
  rewrite !hylo_cata, hylo_map_fusion.
  rewrite <- tau_fusion. simpl. reflexivity.
  apply l_out_in.
Defined.

(** Example 2 from shortcut fusion in calc form [length \o rev ] *)

(* Quadratic reverse *)
Definition rev_alg {A} (a : Alg (ListF A) (list A))
  : App (ListF A) (list A) ~> list A.
Proof.
  refine {| Morphism.app
           := fun x : (App (ListF A) (list A))=>
                match x with
                | MkCont sx kx =>
                    match sx with
                    | s_nil => fun k => (a {| shape := s_nil; cont := k |})
                    | s_cons h =>
                        fun k =>
                          hylo (tau_alg (cons h nil) a) ilist_coalg
                            (k (MkElem tt (tt_cons h)))
                    end kx
                end
         |}.
  Opaque eqRel hylo.
  intros [sx kx] [sy ky] [Exy Kxy]; simpl in *; subst.
  destruct sy as [|hy]; simpl; auto with ffix.
  Transparent eqRel. simpl in Exy; subst.
  apply app_eq; constructor; auto with ffix.
  simpl in Exy; subst; apply app_eq, Kxy; trivial.
  Transparent hylo.
Defined.

Definition reverse {A} : list A ~> list A
  := hylo (rev_alg ilist_alg) ilist_coalg.

Definition example2 {A} : Ext (hylo len_alg ilist_coalg \o @reverse A).
Proof.
  calculate.
  unfold reverse.
  rewrite hylo_fusion_l with (g2 := len_alg).
  2:{
    Opaque hylo.
    intros x.
    destruct x as [[|h] kx].
    - simpl. rewrite hylo_unr; auto with ffix.
    - simpl.
      replace (hylo len_alg ilist_coalg
                 (hylo (tau_alg (h :: nil) ilist_alg) ilist_coalg
                    (kx {| val := tt; Valid := tt_cons h |})))
        with ((hylo len_alg ilist_coalg
               \o hylo (tau_alg (h :: nil) ilist_alg) ilist_coalg)
                (kx {| val := tt; Valid := tt_cons h |})) by reflexivity.
      rewrite <- tau_fusion; simpl.
      induction (kx _) as [|x t Ih]; rewrite hylo_unr; simpl.
      rewrite hylo_unr; simpl; reflexivity.
      rewrite Ih; rewrite hylo_unr at 2; simpl; reflexivity.
      intros [[|h'] k]; simpl; constructor; simpl; auto with ffix.
      + intros e. destruct (dom_nil_false e).
      + intros [[] V1] [[] V2] _; simpl in *.
        rewrite (bool_irrelevance (p_cons eq_refl) V2); reflexivity.
  }
  Transparent hylo.
  unfold len_alg. simpl.
  reflexivity.
Defined.

Module ToExtract.
  Definition ex1 := Eval unfold example1 in @example1.
  Definition ex2 := Eval unfold example2 in @example2.
End ToExtract.


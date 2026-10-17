Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

From Hylo Require Import Hylo.
Require Import Hylo.Utils.

Require Import Hylo.Examples.BTree.
Require Import Hylo.Examples.CList.

From Stdlib Require Import List.
From Stdlib Require Import Sint63.

(* Memoisation tables for a container C, indexed by 'A' *)
(** The container below is equivalent to:
 * [ CoInductive MemoTable `(C : Cont Sc Pc) A
   := Cons { head : A; tail : App C (MemoTable C A) }.
   ]
 *)
Section MemoTable.
  Context `(G : Cont Sg Pg) `{setoid A}.

  Definition MemoShape : Type := A * Sg.
  Definition MemoPos := Pg.
  Instance Memo : Cont MemoShape MemoPos
    := { valid := valid \o pair (snd \o fst) snd }.

  Definition Table := LFix Memo.

  Definition ConsT (x : A * App G Table)
    : App Memo Table :=
    match x with
    | (a, MkCont sx kx) =>
        {| shape := (a, sx);
          cont := fun e : Container.Pos Memo (a, sx) =>
                    match e with
                    | MkElem e V => kx (MkElem e V)
                    end
        |}
    end.
  Lemma ConsT_morph : forall x y, x =e y -> ConsT x =e ConsT y.
  Proof.
    intros [ax [sx kx]] [ay [sy ky]] [Ea [St Kt]]; simpl in *.
    constructor; simpl; auto with ffix.
    intros [v1 V1] [v2 V2] Ev; simpl in *; subst; apply Kt; trivial.
  Qed.
  Definition Cons : A * App G Table ~> App Memo Table
    := Eval unfold ConsT in MkMorph ConsT_morph.

  Definition headT_ (t : Table) : A := fst (shape (l_out t)).
  Definition tailT_ (t : Table) : App G Table :=
    match l_out t with
    | {| shape := (a, st); cont := kt |} =>
        {| shape := st; cont := fun e =>
                                  match e with
                                  | MkElem v V => kt (MkElem v V)
                                  end
        |}
    end.
  Lemma headT_morph : forall x y, x =e y -> headT_ x =e headT_ y.
  Proof.
    intros [[[a sx] kx]] [[[b sy] ky]] [[]]; trivial.
  Qed.
  Definition headT := Eval unfold headT_ in MkMorph headT_morph.

  Lemma tailT_morph : forall x y, x =e y -> tailT_ x =e tailT_ y.
  Proof.
    intros [[[a sx] kx]] [[[b sy] ky]] [[Ea Es] Ek]; constructor; trivial.
    intros [v1 V1] [v2 V2] Eq; simpl in *; subst; apply Ek; trivial.
  Qed.
  Definition tailT := Eval unfold tailT_ in MkMorph tailT_morph.
End MemoTable.
Arguments Table {Sg}%_type_scope {Esh} {Pg}%_type_scope G A%_type_scope {H}.
Arguments Cons & {Sg}%_type_scope {Esh} {Pg}%_type_scope {G}
  {A}%_type_scope {_}.
Arguments headT {Sg}%_type_scope {Esh} {Pg}%_type_scope {G}
  {A}%_type_scope {H}.
Arguments tailT {Sg}%_type_scope {Esh} {Pg}%_type_scope {G}
  {A}%_type_scope {H}.

Definition dyna `{setoid A} `{setoid B} `{C : Cont Sc Pc}
  (a : App C (Table C A) ~> A) (c : RCoalg C B) : B ~> A
  := headT \o hylo (l_in \o Cons \o pair a id) c.

Definition NatF := Sum (K unit) Id.

Lemma valid_inr_tt : valid (F:=NatF) (inr tt, inr tt).
Proof. reflexivity. Qed.
Fixpoint lookupT (x : nat) (t : Table NatF int) {struct x}: option int :=
  match x with
  | 0 => Some (headT_ t)
  | S y =>
      match tailT_ t with
      | MkCont st kt =>
          match st with
          | inl tt => fun _ => None
          | inr tt => fun k => lookupT y (k (MkElem (inr tt) valid_inr_tt))
          end kt
      end
  end.

Lemma lookupT_morph
  : forall x y, x =e y -> forall t t', t =e t' -> lookupT x t =e lookupT y t'.
Proof.
  intros x y Exy; simpl in Exy; subst.
  induction y as [|y Ih]; intros t t' Rt; simpl.
  - f_equal; apply (headT_morph Rt).
  - pose proof (tailT_morph Rt) as Tt; clear Rt.
    destruct tailT_ as [st kt], tailT_ as [st' kt'], Tt as [St Kt].
    simpl in *; destruct st as [[]|[]], st' as [[]|[]];
      try discriminate; try destruct St; trivial.
    apply Ih, Kt; trivial.
Qed.

Definition out_nat (n : nat) : App NatF nat :=
  match n with
  | 0 => MkCont (inl tt) (fun e => 0)
  | S n => MkCont (inr tt) (fun _ => n)
  end.

Lemma out_nat_rec : RecP out_nat.
Proof.
  intros x; induction x as [|x Ih]; constructor; trivial.
  intros [[[]|] V]; simpl in V; discriminate.
Qed.
#[export] Instance out_nat_terminates : Terminates out_nat := out_nat_rec.

Fixpoint max_int acc (l : list int) :=
  match l with
  | h :: t =>
      if (acc <? h)%sint63 then max_int h t
      else max_int acc t
  | nil => acc
  end.

Fixpoint memo_knapsack table wvs :=
  match wvs with
  | nil => nil
  | h :: t =>
      match lookupT (Nat.pred (fst h)) table with
      | Some u => (u + snd h)%sint63 :: memo_knapsack table t
      | None => memo_knapsack table t
      end
  end.

Lemma memo_knapsack_morph wvs :
  forall t1 t2, LFixR t1 t2 -> memo_knapsack t1 wvs = memo_knapsack t2 wvs.
Proof.
  intros t1 t2 Rt; induction wvs as [|[n i] wvs Ih]; simpl; trivial.
  rewrite (lookupT_morph (eq_refl (Nat.pred n)) Rt).
  destruct lookupT; simpl; rewrite ?Ih; reflexivity.
Qed.

Definition knapsack_alg (wvs : list (nat * int))
  (x : App NatF (Table NatF int)) : int
  := match x with
     | MkCont sx kx =>
         match sx with
         | inl tt => fun kx => 0%sint63
         | inr tt =>
             fun kx =>
               let table := kx (MkElem (inr tt) valid_inr_tt) in
               max_int 0 (memo_knapsack table wvs)
         end kx
     end.
Lemma knapsack_alg_morph wvs
  : forall x y, x =e y -> knapsack_alg wvs x =e knapsack_alg wvs y.
Proof.
  intros [sx kx] [sy ky] [Es Ek]; simpl in *.
  destruct sx as [[]|[]], sy as [[]|[]]; try destruct Es; trivial.
  rewrite (memo_knapsack_morph wvs (Ek _ _ eq_refl)); reflexivity.
Qed.

Definition knapsackA (wvs : list (nat * int))
  : App NatF (Table NatF int) ~> int
  := Eval unfold knapsack_alg in MkMorph (knapsack_alg_morph wvs).

Example ex1 wvs : Ext (dyna (knapsackA wvs) out_nat).
Proof.
  calculate.
  unfold dyna, fst, g_in, Cons, pair, out_nat, knapsackA, headT, tailT.
  unfold comp, fst, snd, pair, valid, id, GFix_out.
  unfold hylo, lookupT, headT_, tailT_.
  simpl; reflexivity.
Defined.

Module ToExtract.
  Definition knapsack := Eval unfold ex1 in ex1.
End ToExtract.

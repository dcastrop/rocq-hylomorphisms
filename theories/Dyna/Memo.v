Set Warnings "-bad-template-constraint,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Core.
Require Import Hylo.Schemes.

(** * Memo tables
  *
  * Memo tables for a container [G] with entries in [A] are initial algebras of
  * [Memo G A] ([X = A * G X]). *)
Section MemoDef.
  Context `(G : Cont Sg Pg) `{setoid A}.

  Definition MemoShape : Type := A * Sg.
  Definition MemoPos := Pg.
  Instance Memo : Cont MemoShape MemoPos
    := { valid := valid \o pair (snd \o fst) snd }.

  Definition mcons `{setoid X} : A * App G X ~> App Memo X :=
    morph_of (fun x =>
    match x with
    | (a, MkCont sx kx) =>
        MkCont (a, sx) (fun e : Container.Pos Memo (a, sx) =>
                          match e with MkElem e V => kx (MkElem e V) end)
    end).

  Definition mhead `{setoid X} : App Memo X ~> A
    := morph_of (fun x => Datatypes.fst (shape x)).

  Definition mtail `{setoid X} : App Memo X ~> App G X :=
    morph_of (fun x =>
    match x with
    | MkCont (a, sx) kx =>
        MkCont sx (fun e : Container.Pos G sx =>
                     match e with MkElem e V => kx (MkElem e V) end)
    end).

  Lemma mcons_nat `{setoid X} `{setoid Y} (f : X ~> Y)
    : fmap f \o mcons =e mcons \o pair fst (fmap f \o snd).
  Proof.
    intros [a [s k]]; split; [reflexivity|].
    intros [v1 V1] [v2 V2] Ev; cbn in Ev; subst v2; cbn.
    replace V2 with V1 by apply bool_irrelevance; reflexivity.
  Qed.

  Lemma mhead_fmap `{setoid X} `{setoid Y} (f : X ~> Y)
    : mhead \o fmap f =e mhead.
  Proof. intros x; reflexivity. Qed.
End MemoDef.
Arguments mcons_nat {Sg Esh Pg} G A {H X H0 Y H1} f _.
Arguments mhead_fmap {Sg Esh Pg} G A {H X H0 Y H1} f _.
Arguments Memo {Sg Esh Pg} G A {H}.
Arguments mcons {Sg Esh Pg G A H X _}.
Arguments mhead {Sg Esh Pg G A H X _}.
Arguments mtail {Sg Esh Pg G A H X _}.

(** * Tables of functions
  *
  * [table c f] is the table of [f] along [c]: each node holds [f b] and the
  * tables of the children of [b]. *)
Section Table.
  Context `{G : Cont Sg Pg} `{setoid A} `{setoid B}
    (c : RCoalg G B) (f : B ~> A).

  Lemma table_rec : RecP (mcons \o pair f c).
  Proof.
    intros b; induction (terminating c b) as [b _ Ih]; constructor; cbn.
    destruct (c b) as [s k]; intros [v V]; apply Ih.
  Defined.

  Context `{eT : setoid T} `{!Initial (Memo G A) T}.

  Definition table : B ~> T :=
    rana (Rec (coalg := mcons \o pair f c) table_rec).

  Lemma table_unfold : table =e l_in \o mcons \o pair f (fmap table \o c).
  Proof.
    unfold table at 1; rewrite rana_unfold; fold table.
    arewrite (mcons_nat G A table); intros x; reflexivity.
  Qed.

  Lemma mhead_table : mhead \o l_out \o table =e f.
  Proof.
    rewrite table_unfold at 1; arewrite l_out_in.
    intros x; cbn; destruct (c x); reflexivity.
  Qed.
End Table.
Arguments table {Sg Esh Pg G A H B H0} c f {T eT _}.

(** [table c f] commutes with a step of [c] *)
Lemma table_step `{G : Cont Sg Pg} `{setoid A} `{setoid B} `{eT : setoid T}
  `{!Initial (Memo G A) T} (c : RCoalg G B) (f : B ~> A)
  : mtail \o l_out \o table c f =e fmap (table c f) \o c.
Proof.
  intros x; etransitivity;
    [apply (app_eq mtail), (app_eq l_out), table_unfold|].
  etransitivity; [apply (app_eq mtail), l_out_in|].
  destruct (c x) as [s k]; split; [reflexivity|].
  intros [v1 V1] [v2 V2] Ev; cbn in Ev; subst v2; cbn.
  replace V2 with V1 by apply bool_irrelevance; reflexivity.
Qed.

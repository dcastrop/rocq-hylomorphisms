Require Import Hylo.Extraction.Common.
Require Import Hylo.Examples.ShortcutFusion.

Definition ex1_code {A B} (f : A ~> B) ys :=
  Eval simpl in (fun xs => example1 f ys xs).
Definition ex2_code {A} := Eval simpl in (fun xs : list A => example2 xs).

Set Extraction Flag 2047.
Extraction "shortcutfusion" ex1_code ex2_code.

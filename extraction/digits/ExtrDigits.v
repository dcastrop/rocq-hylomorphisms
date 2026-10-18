Require Import Hylo.Extraction.Common.
Require Import Hylo.Examples.Digits.

Opaque Hylo.Utils.wf_lt.
Definition fast_power_code := Eval simpl in (fun x n => fast_power x n).
Definition sumsq_fold_code := Eval simpl in (fun n => sumsq_fold n).
Definition sumsq_unfold_code := Eval simpl in (fun n => sumsq_unfold n).

Set Extraction Flag 2047.
Extraction "digits" fast_power_code sumsq_fold_code sumsq_unfold_code.

Require Import Hylo.Extraction.Common.
Require Import Hylo.Examples.BTree.
Require Import Hylo.Examples.QSort.

Extraction Inline posL.
Extraction Inline posR.
Opaque Hylo.Utils.wf_lt.
Definition qsort_code := Eval simpl in (fun x => qsort x).
Definition qsort_times_two_code := Eval simpl in (fun x => qsort_times_two x).

Set Extraction Flag 2047.
Extraction "qsort" qsort_code qsort_times_two_code.

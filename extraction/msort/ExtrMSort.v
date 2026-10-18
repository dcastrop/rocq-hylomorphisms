Require Import Hylo.Extraction.Common.
Require Import Hylo.Examples.MSort.

Extract Inlined Constant Nat.leb => "(<=)".
Opaque Hylo.Utils.wf_lt.
Definition msort_code := Eval simpl in (fun x => msort x).

Set Extraction Flag 2047.
Extraction "msort" msort_code.

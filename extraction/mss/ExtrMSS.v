Require Import Hylo.Extraction.Common.
Require Import Hylo.Extraction.ExtrBigint.
Require Import Hylo.MonoidAlg.
Require Import Hylo.Examples.ListLaws.
Require Import Hylo.Examples.MSS.

Extraction Inline tup max_monoid plus_monoid.
Set Extraction Flag 2047.
Definition mss_code := Eval simpl in (fun xs => mss_linear xs).

Extraction "mss" mss_code.

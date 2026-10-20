Require Import Hylo.Extraction.Common.
Require Import Hylo.Extraction.ExtrDyna.
From Stdlib Require ExtrOcamlNatInt ExtrOCamlPArray.
Require Import Hylo.Hylo.
Require Import Hylo.Utils.
Require Import Hylo.Dyna.
Require Import Hylo.Examples.ArrayTable.
Require Import Hylo.Examples.Knapsack.

Definition knapsack_code wvs :=
  ltac:(let t := eval cbv beta iota delta
                  [knapsack_arr ATab_initial atab_out atab_out_c atab_out_
                   atab_in atab_in_ knap_alg knap_alg_ map_some]
                in (fun n => knapsack_arr wvs n) in
        let t := eval dyna_red in t in exact t).

Extraction NoInline PrimArray.array.
Extract Inlined Constant PrimArray.make => "Parray.make".
Extract Inlined Constant PrimArray.get => "Parray.get".
Extract Inlined Constant PrimArray.set => "Parray.set".
Set Extraction Flag 2047.
Extraction "knapsack" knapsack_code.

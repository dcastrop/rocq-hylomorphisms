Require Import Hylo.Extraction.Common.
From Stdlib Require ExtrOcamlNatInt ExtrOCamlPArray.
Require Import Hylo.Examples.Dyna.
Require Import Hylo.Examples.Knapsack.

Definition knapsack_code wvs :=
  Eval cbv beta iota delta [knapsack_arr int_hylo int_hylo_acc is_zero arr_alg arr_alg_
                            knapsackArr knapsack_arr_ Morphism.app]
  in fun n => knapsack_arr wvs n.

Extraction NoInline PrimArray.array.
Extract Inlined Constant PrimArray.make => "Parray.make".
Extract Inlined Constant PrimArray.get => "Parray.get".
Extract Inlined Constant PrimArray.set => "Parray.set".
Set Extraction Flag 2047.
Extraction "knapsack" knapsack_code.

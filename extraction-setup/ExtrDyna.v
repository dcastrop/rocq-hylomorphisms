Require Import Hylo.Extraction.Common.
Require Import Hylo.Hylo.
Require Import Hylo.Dyna.

(** Unfolds the generic dynamorphism machinery before extraction. No [zeta]:
  * it would substitute the shared child in [memo_alg_]. *)
Declare Reduction dyna_red :=
  cbv beta iota delta [comp Morphism.app Datatypes.fst coalg mk_wf_coalg
                       hylo cata flip papp
                       l_in l_out mhead mcons memo_alg memo_alg_
                       out_int out_int_c fmap fmapA
                       look_tbl look_tbl_ pwalk int_paths
                       iwalk_from iwalk iwalk_alg_ at_pos].

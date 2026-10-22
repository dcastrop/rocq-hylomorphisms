Set Warnings "-deprecated-transitive-library-file".
Generalizable All Variables.

Require Export Hylo.Extraction.Common.
Require Import Hylo.Hylo.

(** Unfolds the generic dynamorphism machinery before extraction. No [zeta]:
  * it would substitute shared [let]s, duplicating the work they bind. *)
Declare Reduction dyna_red :=
  cbv beta iota delta [comp Morphism.app Morphism.id coalg mk_wf_coalg
                       hylo cata flip papp hylo_cps hylo_cps_def ccoalg
                       RecF_inv_eq convoy
                       l_in l_out mhead mcons mtail
                       out_int out_int_c fmap fmapA nat_child
                       look_with look_with_
                       iwalk_from iwalk iwalk_alg_ iwalk_child option_map
                       mconcat opt_cons members proper_rcoalg proper_morph
                       reverse_coercion loop loop_c loop_c_ loop_alg
                       loop_alg_ memo_step memo_base nat_next nat_leaf natural
                       eta natT
                       f_nat_eta].

(** Then computes container validity. [cbn] unfolds these only where that
  * reduces, so the types (e.g. [Pos NatF s]) stay folded; no [zeta]. *)
Declare Reduction valid_red :=
  cbn beta iota delta [valid Memo NatF LoopF Sum K Id
                       Morphism.app comp Morphism.pair Morphism.fst
                       Morphism.snd Datatypes.fst Datatypes.snd
                       Container.shape Container.cont].

(* Monoid algebras, unfolded so that their [Finite] instances are exposed *)
#[export] Hint Unfold malg malg_ : unfold_code.

(* Checking a reduced function against the original (in [finished] and at
   [Qed]) must not unfold termination measures: [Uint63.to_Z] on a variable
   does not terminate in practice *)
Strategy opaque [Uint63.to_Z wf_lt].

(** [finished] instantiates a derived function with the result reduced by
  * [dyna_red] and [valid_red], after unfolding [unfold_code]. *)
Ltac specialise ::=
  repeat progress autounfold with unfold_code;
  lazymatch goal with
  | |- ?t =e ?e =>
      let r := eval dyna_red in (fun x => app t x) in
      let r := eval valid_red in r in
      refine (e_trans (y := @MkMorph _ _ _ _ r (app_eq t)) _ _); [reflexivity|]
  end.

From Stdlib Require Import ZArith Extraction.

(** [Z] and [positive] as Zarith's [Z.t], through the alias [Bigint] (a local
  * module [Z] would shadow Zarith's). Operations are realized under both
  * their [BinInt]/[BinPos] names and the [IntDef]/[PosDef] constants they
  * alias: extraction follows the bodies of the latter for dependencies. *)

Extract Inductive positive => "Bigint.t"
  [ "(fun p -> Bigint.succ (Bigint.shift_left p 1))" "(fun p -> Bigint.shift_left p 1)" "Bigint.one" ]
  "(fun f1 f2 f3 p -> if Bigint.equal p Bigint.one then f3 () else
     if Bigint.is_odd p then f1 (Bigint.shift_right p 1) else f2 (Bigint.shift_right p 1))".

Extract Inductive Z => "Bigint.t" [ "Bigint.zero" "(fun p -> p)" "Bigint.neg" ]
  "(fun f0 fp fn z -> let s = Bigint.sign z in
     if s = 0 then f0 () else if s > 0 then fp z else fn (Bigint.neg z))".

Extract Inlined Constant Z.add => "Bigint.add".
Extract Inlined Constant IntDef.Z.add => "Bigint.add".
Extract Inlined Constant Z.sub => "Bigint.sub".
Extract Inlined Constant IntDef.Z.sub => "Bigint.sub".
Extract Inlined Constant Z.mul => "Bigint.mul".
Extract Inlined Constant IntDef.Z.mul => "Bigint.mul".
Extract Inlined Constant Z.opp => "Bigint.neg".
Extract Inlined Constant IntDef.Z.opp => "Bigint.neg".
Extract Inlined Constant Z.max => "Bigint.max".
Extract Inlined Constant IntDef.Z.max => "Bigint.max".
Extract Inlined Constant Z.min => "Bigint.min".
Extract Inlined Constant IntDef.Z.min => "Bigint.min".
Extract Inlined Constant Z.eqb => "Bigint.equal".
Extract Inlined Constant IntDef.Z.eqb => "Bigint.equal".
Extract Inlined Constant Z.leb => "Bigint.leq".
Extract Inlined Constant IntDef.Z.leb => "Bigint.leq".
Extract Inlined Constant Z.ltb => "Bigint.lt".
Extract Inlined Constant IntDef.Z.ltb => "Bigint.lt".
Extract Inlined Constant Z.double => "(fun x -> Bigint.shift_left x 1)".
Extract Inlined Constant IntDef.Z.double => "(fun x -> Bigint.shift_left x 1)".
Extract Inlined Constant Z.succ_double => "(fun x -> Bigint.succ (Bigint.shift_left x 1))".
Extract Inlined Constant IntDef.Z.succ_double => "(fun x -> Bigint.succ (Bigint.shift_left x 1))".
Extract Inlined Constant Z.pred_double => "(fun x -> Bigint.pred (Bigint.shift_left x 1))".
Extract Inlined Constant IntDef.Z.pred_double => "(fun x -> Bigint.pred (Bigint.shift_left x 1))".
Extract Inlined Constant Z.pos_sub => "Bigint.sub".
Extract Inlined Constant IntDef.Z.pos_sub => "Bigint.sub".
Extract Inlined Constant Z.compare => "(fun x y -> let c = Bigint.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".
Extract Inlined Constant IntDef.Z.compare => "(fun x y -> let c = Bigint.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".
Extract Inlined Constant Pos.succ => "Bigint.succ".
Extract Inlined Constant PosDef.Pos.succ => "Bigint.succ".
Extract Inlined Constant Pos.add => "Bigint.add".
Extract Inlined Constant PosDef.Pos.add => "Bigint.add".
Extract Inlined Constant Pos.add_carry => "(fun x y -> Bigint.succ (Bigint.add x y))".
Extract Inlined Constant PosDef.Pos.add_carry => "(fun x y -> Bigint.succ (Bigint.add x y))".
Extract Inlined Constant Pos.pred_double => "(fun x -> Bigint.pred (Bigint.shift_left x 1))".
Extract Inlined Constant PosDef.Pos.pred_double => "(fun x -> Bigint.pred (Bigint.shift_left x 1))".
Extract Inlined Constant Pos.compare_cont => "(fun r x y -> let c = Bigint.compare x y in if c = 0 then r else if c < 0 then Lt else Gt)".
Extract Inlined Constant PosDef.Pos.compare_cont => "(fun r x y -> let c = Bigint.compare x y in if c = 0 then r else if c < 0 then Lt else Gt)".
Extract Inlined Constant Pos.compare => "(fun x y -> let c = Bigint.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".
Extract Inlined Constant PosDef.Pos.compare => "(fun x y -> let c = Bigint.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".

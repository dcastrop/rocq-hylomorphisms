Set Warnings "-deprecated-transitive-library-file".
Require Export Hylo.Core.

From Stdlib Require Extraction.
From Stdlib Require ExtrOcamlBasic.
From Stdlib Require ExtrOCamlInt63.
From Stdlib Require ExtrOCamlPArray.
#[global] Set Extraction TypeExpand.
#[global] Set Extraction Flag 2047.
(* Extracted files go to the current directory, as by default (without the
   warning) *)
#[global] Set Extraction Output Directory ".".
Extraction Inline val.

Extract Inlined Constant Uint63.add => "Uint63.add".
Extract Inlined Constant Uint63.sub => "Uint63.sub".
Extract Inlined Constant Uint63.mul => "Uint63.mul".
Extract Inlined Constant Uint63.div => "Uint63.div".
Extract Inlined Constant Uint63.mod => "Uint63.rem".
Extract Inlined Constant Uint63.eqb => "Uint63.equal".
Extract Inlined Constant Uint63.ltb => "Uint63.lt".
Extract Inlined Constant Uint63.leb => "Uint63.le".
Extract Inlined Constant Sint63.ltb => "Uint63.lts".
Extract Inlined Constant Sint63.leb => "Uint63.les".

Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Extraction NoInline PrimArray.array.
Extract Inlined Constant PrimArray.make => "Parray.make".
Extract Inlined Constant PrimArray.get => "Parray.get".
Extract Inlined Constant PrimArray.set => "Parray.set".

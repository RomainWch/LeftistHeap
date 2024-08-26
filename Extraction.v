From LEFTISTHEAP Require Import Definitions.
Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
(* Extraction lheap.
Extraction mergep.  *)
(* Recursive Extraction merge. *)
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction "lheap" isEmpty merge insert deleteMin.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.MinskyMachines Require Import MM MM_undec.
From Undecidability.FRACTRAN Require Import FRACTRAN Reductions.MM_FRACTRAN.
Check FRACTRAN_REG_undec.

Theorem FRACTRAN_REG_undec : undecidable FRACTRAN_REG_HALTING.
Proof.
apply (undecidability_from_reducibility MM_HALTING_undec).
Admitted.

Theorem FRACTRAN_undec : undecidable FRACTRAN_HALTING.
Proof.
apply (undecidability_from_reducibility FRACTRAN_REG_undec).
apply FRACTRAN_REG_FRACTRAN_HALTING.

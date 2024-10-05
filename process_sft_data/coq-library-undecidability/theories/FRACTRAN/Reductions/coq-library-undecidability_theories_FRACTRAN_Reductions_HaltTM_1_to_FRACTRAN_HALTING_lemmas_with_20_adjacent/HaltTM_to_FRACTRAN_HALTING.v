Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.TM.TM.
From Undecidability.MinskyMachines Require Import MM HaltTM_1_to_MM.
From Undecidability.FRACTRAN Require Import FRACTRAN Reductions.MM_FRACTRAN.

Lemma HaltTM_to_FRACTRAN_REG_HALTING : HaltTM 1 ⪯ FRACTRAN_REG_HALTING.
Proof.
apply (reduces_transitive HaltTM_to_MM_HALTING).
Admitted.

Lemma HaltTM_to_FRACTRAN_HALTING : HaltTM 1 ⪯ FRACTRAN_HALTING.
Proof.
apply (reduces_transitive HaltTM_to_MM_HALTING).
exact MM_FRACTRAN_HALTING.

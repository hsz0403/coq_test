Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.FRACTRAN Require Import FRACTRAN FRACTRAN_undec.
From Undecidability.MinskyMachines Require Import MMA FRACTRAN_to_MMA2.
Lemma MMA2_HALTING_undec : undecidable MMA2_HALTING.
Proof.
apply (undecidability_from_reducibility FRACTRAN_REG_undec).
apply FRACTRAN_REG_MMA2_HALTING.
Qed.
Check MMA2_HALTING_undec.
Lemma MMA2_HALTS_ON_ZERO_undec : undecidable MMA2_HALTS_ON_ZERO.
Proof.
apply (undecidability_from_reducibility FRACTRAN_REG_undec).
apply FRACTRAN_REG_MMA2_HALTS_ON_ZERO.
Qed.
Check MMA2_HALTS_ON_ZERO_undec.
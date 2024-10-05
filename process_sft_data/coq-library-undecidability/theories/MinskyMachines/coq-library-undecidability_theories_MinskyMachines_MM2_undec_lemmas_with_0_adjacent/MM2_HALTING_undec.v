Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.MinskyMachines Require Import MMA MM2 MMA2_undec MMA2_to_MM2.
Check MM2_HALTING_undec.
Check MM2_HALTS_ON_ZERO_undec.

Lemma MM2_HALTING_undec : undecidable MM2_HALTING.
Proof.
apply (undecidability_from_reducibility MMA2_HALTING_undec).
apply MMA2_MM2_HALTING.

Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.MinskyMachines Require Import MMA MMA2_undec ndMM2 MMA2_to_ndMM2_ACCEPT.

Theorem ndMM2_undec : undecidable (@ndMM2_ACCEPT nat).
Proof.
apply (undecidability_from_reducibility MMA2_HALTS_ON_ZERO_undec).
apply MMA2_to_ndMM2_ACCEPT.reduction.

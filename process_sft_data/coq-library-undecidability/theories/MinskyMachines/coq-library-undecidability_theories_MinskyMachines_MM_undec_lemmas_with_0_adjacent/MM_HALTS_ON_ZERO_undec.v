Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.StackMachines Require Import BSM BSM_undec.
From Undecidability.MinskyMachines Require Import MM Reductions.BSM_MM.

Lemma MM_HALTS_ON_ZERO_undec : undecidable MM_HALTS_ON_ZERO.
Proof.
apply (undecidability_from_reducibility BSM_undec).
apply BSM_MM_HALTS_ON_ZERO.

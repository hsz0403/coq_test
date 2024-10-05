Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.TM.TM_undec.
Require Undecidability.TM.Reductions.HaltTM_1_to_HaltSBTM.
Require Undecidability.TM.Reductions.HaltSBTM_to_HaltSBTMu.

Lemma HaltSBTM_undec : undecidable SBTM.HaltSBTM.
Proof.
apply (undecidability_from_reducibility HaltTM_1_undec).
eapply HaltTM_1_to_HaltSBTM.reduction.

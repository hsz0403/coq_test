Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.TM.TM_undec.
Require Undecidability.TM.Reductions.HaltTM_1_to_HaltSBTM.
Require Undecidability.TM.Reductions.HaltSBTM_to_HaltSBTMu.

Lemma HaltSBTMu_undec : undecidable SBTM.HaltSBTMu.
Proof.
apply (undecidability_from_reducibility HaltSBTM_undec).
apply HaltSBTM_to_HaltSBTMu.reduction.

Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.StringRewriting.SR.
Require Import Undecidability.TM.SBTM_undec.
From Undecidability.StringRewriting.Reductions Require HaltSBTMu_to_SRH SRH_to_SR HaltSBTMu_to_TSR.
Check SRH_undec.
Check SR_undec.
Check SR_undec.

Lemma SR_undec : undecidable SR.
Proof.
apply (undecidability_from_reducibility SRH_undec).
exact SRH_to_SR.reduction.

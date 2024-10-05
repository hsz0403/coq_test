Require Import Undecidability.CFG.CFP.
From Undecidability.CFG.Reductions Require PCP_to_CFPP PCP_to_CFPI.
Require Import Undecidability.Synthetic.Undecidability.
Require Undecidability.PCP.PCP_undec.

Lemma CFPI_undec : undecidable CFPI.
Proof.
eapply undecidability_from_reducibility.
exact PCP_undec.PCP_undec.
exact PCP_to_CFPI.reduction.

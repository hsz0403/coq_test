Require Import Undecidability.CFG.CFG.
From Undecidability.CFG.Reductions Require CFPP_to_CFP CFPI_to_CFI.
Require Import Undecidability.Synthetic.Undecidability.
Require Undecidability.CFG.CFP_undec.
Check CFP_undec.
Check CFI_undec.

Lemma CFI_undec : undecidable CFI.
Proof.
eapply undecidability_from_reducibility.
exact CFP_undec.CFPI_undec.
Admitted.

Lemma CFP_undec : undecidable CFP.
Proof.
eapply undecidability_from_reducibility.
exact CFP_undec.CFPP_undec.
exact CFPP_to_CFP.reduction.

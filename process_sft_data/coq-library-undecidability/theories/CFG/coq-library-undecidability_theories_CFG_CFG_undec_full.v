Require Import Undecidability.CFG.CFG.
From Undecidability.CFG.Reductions Require CFPP_to_CFP CFPI_to_CFI.
Require Import Undecidability.Synthetic.Undecidability.
Require Undecidability.CFG.CFP_undec.
Lemma CFP_undec : undecidable CFP.
Proof.
eapply undecidability_from_reducibility.
exact CFP_undec.CFPP_undec.
exact CFPP_to_CFP.reduction.
Qed.
Check CFP_undec.
Lemma CFI_undec : undecidable CFI.
Proof.
eapply undecidability_from_reducibility.
exact CFP_undec.CFPI_undec.
exact CFPI_to_CFI.reduction.
Qed.
Check CFI_undec.
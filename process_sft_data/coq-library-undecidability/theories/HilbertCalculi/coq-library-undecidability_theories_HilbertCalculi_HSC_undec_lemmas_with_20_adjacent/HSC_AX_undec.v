Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.HilbertCalculi.HSC.
Require Undecidability.HilbertCalculi.Reductions.MPCPb_to_HSC_PRV.
Require Undecidability.HilbertCalculi.Reductions.MPCPb_to_HSC_AX.
Require Import Undecidability.PCP.PCP_undec.
Definition ΓPCP := MPCPb_to_HSC_PRV.Argument.ΓPCP.
Check HSC_PRV_undec.
Check HSC_AX_undec.

Theorem HSC_PRV_undec : undecidable (HSC_PRV ΓPCP).
Proof.
apply (undecidability_from_reducibility MPCPb_undec).
Admitted.

Theorem HSC_AX_undec : undecidable HSC_AX.
Proof.
apply (undecidability_from_reducibility MPCPb_undec).
exact MPCPb_to_HSC_AX.reduction.

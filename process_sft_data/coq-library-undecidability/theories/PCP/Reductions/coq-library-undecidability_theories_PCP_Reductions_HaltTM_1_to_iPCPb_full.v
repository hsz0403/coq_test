Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.TM.TM.
Require Import Undecidability.PCP.PCP.
Require Undecidability.PCP.Reductions.HaltTM_1_to_PCP.
Require Import Undecidability.PCP.Reductions.PCP_to_PCPb.
Require Import Undecidability.PCP.Reductions.PCPb_iff_iPCPb.
Theorem reduction : HaltTM 1 ⪯ iPCPb.
Proof.
apply (reduces_transitive HaltTM_1_to_PCP.reduction).
apply (reduces_transitive PCP_to_PCPb.reduction).
exact PCPb_iff_iPCPb.reductionLR.
Qed.
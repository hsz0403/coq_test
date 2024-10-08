Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.PCP.Reductions Require SR_to_MPCP MPCP_to_MPCPb MPCP_to_PCP PCP_to_PCPb PCPb_iff_iPCPb PCPb_iff_dPCPb.
Require Undecidability.StringRewriting.SR_undec.
Lemma MPCP_undec : undecidable MPCP.
Proof.
apply (undecidability_from_reducibility SR_undec.SR_undec).
exact SR_to_MPCP.reduction.
Qed.
Check MPCP_undec.
Lemma MPCPb_undec : undecidable MPCPb.
Proof.
apply (undecidability_from_reducibility MPCP_undec).
exact MPCP_to_MPCPb.reduction.
Qed.
Check MPCPb_undec.
Lemma PCP_undec : undecidable PCP.
Proof.
apply (undecidability_from_reducibility MPCP_undec).
exact MPCP_to_PCP.reduction.
Qed.
Check PCP_undec.
Lemma PCPb_undec : undecidable PCPb.
Proof.
apply (undecidability_from_reducibility PCP_undec).
exact PCP_to_PCPb.reduction.
Qed.
Check PCPb_undec.
Lemma iPCPb_undec : undecidable iPCPb.
Proof.
apply (undecidability_from_reducibility PCPb_undec).
exists id.
exact PCPb_iff_iPCPb.PCPb_iff_iPCPb.
Qed.
Check iPCPb_undec.
Lemma dPCPb_undec : undecidable dPCPb.
Proof.
apply (undecidability_from_reducibility PCPb_undec).
exists id.
exact PCPb_iff_dPCPb.PCPb_iff_dPCPb.
Qed.
Check dPCPb_undec.
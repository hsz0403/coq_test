Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.PCP.Reductions Require SR_to_MPCP MPCP_to_MPCPb MPCP_to_PCP PCP_to_PCPb PCPb_iff_iPCPb PCPb_iff_dPCPb.
Require Undecidability.StringRewriting.SR_undec.
Check MPCP_undec.
Check MPCPb_undec.
Check PCP_undec.
Check PCPb_undec.
Check iPCPb_undec.
Check dPCPb_undec.

Lemma MPCPb_undec : undecidable MPCPb.
Proof.
apply (undecidability_from_reducibility MPCP_undec).
Admitted.

Lemma PCP_undec : undecidable PCP.
Proof.
apply (undecidability_from_reducibility MPCP_undec).
Admitted.

Lemma PCPb_undec : undecidable PCPb.
Proof.
apply (undecidability_from_reducibility PCP_undec).
Admitted.

Lemma iPCPb_undec : undecidable iPCPb.
Proof.
apply (undecidability_from_reducibility PCPb_undec).
exists id.
Admitted.

Lemma dPCPb_undec : undecidable dPCPb.
Proof.
apply (undecidability_from_reducibility PCPb_undec).
exists id.
Admitted.

Lemma MPCP_undec : undecidable MPCP.
Proof.
apply (undecidability_from_reducibility SR_undec.SR_undec).
exact SR_to_MPCP.reduction.

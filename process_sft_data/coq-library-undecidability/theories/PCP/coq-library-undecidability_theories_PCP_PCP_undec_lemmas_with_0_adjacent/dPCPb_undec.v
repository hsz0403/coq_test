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

Lemma dPCPb_undec : undecidable dPCPb.
Proof.
apply (undecidability_from_reducibility PCPb_undec).
exists id.
exact PCPb_iff_dPCPb.PCPb_iff_dPCPb.

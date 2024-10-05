Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.PCP Require Import PCP Util.Facts PCPX_iff_dPCP.

Lemma reductionLR : PCPb ⪯ dPCPb.
Proof.
exists id.
exact PCPb_iff_dPCPb.

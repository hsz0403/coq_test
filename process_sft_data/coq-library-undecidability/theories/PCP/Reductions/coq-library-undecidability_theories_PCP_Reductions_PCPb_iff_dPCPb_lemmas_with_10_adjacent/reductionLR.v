Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.PCP Require Import PCP Util.Facts PCPX_iff_dPCP.

Lemma PCPb_iff_dPCPb P : PCPb P <-> dPCPb P.
Proof.
Admitted.

Lemma reductionRL : dPCPb ⪯ PCPb.
Proof.
exists id.
intro.
Admitted.

Lemma reductionLR : PCPb ⪯ dPCPb.
Proof.
exists id.
exact PCPb_iff_dPCPb.

Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.PCP Require Import PCP Util.Facts PCPX_iff_dPCP.

Lemma reductionLR : PCPb ⪯ dPCPb.
Proof.
exists id.
Admitted.

Lemma reductionRL : dPCPb ⪯ PCPb.
Proof.
exists id.
intro.
Admitted.

Lemma PCPb_iff_dPCPb P : PCPb P <-> dPCPb P.
Proof.
apply PCPX_iff_dPCP.

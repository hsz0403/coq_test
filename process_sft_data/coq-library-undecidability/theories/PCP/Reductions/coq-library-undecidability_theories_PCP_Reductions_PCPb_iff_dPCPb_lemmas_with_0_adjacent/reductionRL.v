Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.PCP Require Import PCP Util.Facts PCPX_iff_dPCP.

Lemma reductionRL : dPCPb ⪯ PCPb.
Proof.
exists id.
intro.
now rewrite PCPb_iff_dPCPb.

Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.PCP Require Import PCP Util.Facts PCPX_iff_dPCP.

Lemma PCPb_iff_dPCPb P : PCPb P <-> dPCPb P.
Proof.
apply PCPX_iff_dPCP.

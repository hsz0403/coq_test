Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Reductions.PCPX_iff_dPCP.
Require Import Undecidability.Synthetic.Definitions.

Lemma reductionLR : PCPb ⪯ BPCP.
Proof.
exists id; exact PCPb_iff_BPCP.

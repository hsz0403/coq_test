Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Reductions.PCPX_iff_dPCP.
Require Import Undecidability.Synthetic.Definitions.

Lemma PCPb_iff_BPCP P : PCPb P <-> BPCP P.
Proof.
unfold PCPb; rewrite PCPX_iff_dPCP; split.
-
intros (u & Hu); constructor 1 with u; trivial.
-
Admitted.

Lemma reductionLR : PCPb ⪯ BPCP.
Proof.
Admitted.

Lemma reductionRL : BPCP ⪯ PCPb.
Proof.
exists id; intro; now rewrite PCPb_iff_BPCP.

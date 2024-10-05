Require Import List.
From Undecidability.Shared.Libs.DLW Require Import utils.
Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.TM.TM.
From Undecidability.TM Require Import TM SBTM Reductions.HaltTM_1_to_HaltSBTM Reductions.HaltSBTM_to_HaltSBTMu.
From Undecidability.StringRewriting Require Import SR HaltSBTMu_to_SRH SRH_to_SR.
From Undecidability.PCP Require Import PCP.
From Undecidability.PCP.Reductions Require Import SR_to_MPCP MPCP_to_PCP PCP_to_PCPb PCPb_iff_iPCPb.
Import ReductionChainNotations UndecidabilityNotations.

Lemma PCP_chain_PCPb : ⎩PCP ⪯ₘ PCPb⎭.
Proof.
apply PCP_chain_iPCPb.

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.ZF_undec.
Require Import Undecidability.FOL.binZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_ZFeq PCPb_to_ZFD PCPb_to_binZF.
From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Corollary undecidable_entailment_binZF : undecidable entailment_binZF.
Proof.
apply (undecidability_from_reducibility PCPb_undec), PCPb_entailment_binZF.

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts Aczel_CE Aczel_TD ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZFeq PCPb_to_ZF PCPb_to_ZFD.
From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Theorem PCPb_entailment_ZFeq' : PCPb ⪯ entailment_ZFeq'.
Proof.
exists solvable.
intros B.
split; intros H.
-
eapply PCP_ZFD, soundness in H.
intros D M rho H'.
apply H, H'.
-
now apply PCP_ZFeq'; try apply intensional_model.

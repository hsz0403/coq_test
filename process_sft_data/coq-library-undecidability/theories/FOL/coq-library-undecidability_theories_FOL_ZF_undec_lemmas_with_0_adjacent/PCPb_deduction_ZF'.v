Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts Aczel_CE Aczel_TD ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZFeq PCPb_to_ZF PCPb_to_ZFD.
From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Theorem PCPb_deduction_ZF' : PCPb ⪯ deduction_ZF'.
Proof.
exists solvable.
intros B.
split; try apply PCP_ZFD.
intros H' % soundness.
apply PCP_ZFeq'; try apply intensional_model.
intros D M rho H.
apply H', H.

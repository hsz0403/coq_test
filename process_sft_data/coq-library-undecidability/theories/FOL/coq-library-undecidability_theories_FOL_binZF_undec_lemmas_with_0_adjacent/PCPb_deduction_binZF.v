Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.ZF_undec.
Require Import Undecidability.FOL.binZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_ZFeq PCPb_to_ZFD PCPb_to_binZF.
From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Theorem PCPb_deduction_binZF : PCPb ⪯ deduction_binZF.
Proof.
exists (fun B => rm_const_fm (solvable B)).
intros B.
split; intros H.
-
now apply (@PCP_ZFD intu), (@rm_const_prv intu nil) in H.
-
apply PCP_ZFeq'; try apply intensional_model.
apply soundness in H.
intros V M rho HM.
apply min_correct; trivial.
apply H.
now apply min_axioms'.

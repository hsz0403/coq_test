Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.ZF_undec.
Require Import Undecidability.FOL.minZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts Aczel_CE Aczel_TD ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZFeq PCPb_to_minZFeq PCPb_to_ZF PCPb_to_ZFD PCPb_to_binZF PCPb_to_minZF.
From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Theorem PCPb_entailment_minZFeq' : PCPb ⪯ entailment_minZFeq'.
Proof.
exists (fun B => rm_const_fm (solvable B)).
intros B.
split; intros H.
-
apply (@PCP_ZFD intu), (@rm_const_prv intu nil), soundness in H.
intros D M rho H'.
apply H, H'.
-
apply PCP_ZFeq'; try apply intensional_model.
intros V M rho HM.
apply PCPb_to_minZFeq.min_correct; trivial.
apply H.
now apply PCPb_to_minZFeq.min_axioms'.

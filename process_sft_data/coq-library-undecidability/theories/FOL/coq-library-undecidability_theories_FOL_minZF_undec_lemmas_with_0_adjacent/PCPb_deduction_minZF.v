Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.ZF_undec.
Require Import Undecidability.FOL.minZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts Aczel_CE Aczel_TD ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZFeq PCPb_to_minZFeq PCPb_to_ZF PCPb_to_ZFD PCPb_to_binZF PCPb_to_minZF.
From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Theorem PCPb_deduction_minZF : (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> PCPb ⪯ deduction_minZF.
Proof.
intros (V & M & H1 & H2 & H3).
exists (fun B => rm_const_fm (solvable B)).
intros B.
split; intros H.
-
exists minZFeq'.
split; auto using minZFeq.
now apply (@PCP_ZFD intu), (@rm_const_prv intu nil) in H.
-
eapply tsoundness with (I := @min_model V M) (rho := fun _ => ∅) in H.
rewrite <- min_correct in H; trivial; auto using ZF.
rewrite PCPb_iff_dPCPb.
eapply PCP_ZF2 in H2 as [s Hs]; trivial; try apply H; auto using ZF.
now exists s.
apply extensional_eq_min; auto.
apply min_axioms; auto using ZF.

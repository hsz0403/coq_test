Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts Aczel_CE Aczel_TD ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZFeq PCPb_to_ZF PCPb_to_ZFD.
From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

Theorem PCPb_deduction_ZF : (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> PCPb ⪯ deduction_ZF.
Proof.
intros (V & M & H1 & H2 & H3).
exists solvable.
intros B.
split.
-
intros H % (@PCP_ZFD intu).
exists ZFeq'.
split; eauto using ZFeq.
-
intros H'.
specialize (tsoundness H').
clear H'.
intros H'.
apply PCPb_iff_dPCPb.
eapply PCP_ZF2; eauto using ZF.
apply (H' V M (fun _ => ∅)).
intros psi [].
+
apply extensional_eq; eauto using ZF.
+
apply H3.
constructor 2.
+
apply H3.
constructor 3.

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.FOL Require Import FOL Util.Kripke Util.Deduction Util.Syntax Util.Tarski PCPb_to_FOL.
From Undecidability.PCP Require Import PCP Reductions.PCPb_iff_dPCPb.
Section kvalidity.
Local Definition BSRS := list (card bool).
Variable R : BSRS.
Context {ff : falsity_flag}.
End kvalidity.

Theorem BPCP_kprv : PCPb R <-> nil ⊢I (F R).
Proof.
rewrite PCPb_iff_dPCPb.
split.
-
apply BPCP_prv'.
-
intros H % ksoundness'.
rewrite <- PCPb_iff_dPCPb.
now apply (BPCP_valid R), kvalid_valid.

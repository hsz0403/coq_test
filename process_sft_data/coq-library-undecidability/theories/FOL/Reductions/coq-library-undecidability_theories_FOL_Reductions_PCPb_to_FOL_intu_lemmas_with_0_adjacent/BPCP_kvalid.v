From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.FOL Require Import FOL Util.Kripke Util.Deduction Util.Syntax Util.Tarski PCPb_to_FOL.
From Undecidability.PCP Require Import PCP Reductions.PCPb_iff_dPCPb.
Section kvalidity.
Local Definition BSRS := list (card bool).
Variable R : BSRS.
Context {ff : falsity_flag}.
End kvalidity.

Theorem BPCP_kvalid : PCPb R <-> kvalid (F R).
Proof.
split.
-
now intros H % BPCP_kprv % ksoundness'.
-
intros H % kvalid_valid.
now apply (BPCP_valid R).

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.FOL Require Import FOL Util.Kripke Util.Deduction Util.Syntax Util.Tarski PCPb_to_FOL.
From Undecidability.PCP Require Import PCP Reductions.PCPb_iff_dPCPb.
Section kvalidity.
Local Definition BSRS := list (card bool).
Variable R : BSRS.
Context {ff : falsity_flag}.
End kvalidity.

Theorem BPCP_ksatis R : ~ PCPb R <-> ksatis (¬ F R).
Proof.
split.
-
intros H % (BPCP_satis R).
now apply ksatis_satis.
-
intros (D & M & u & rho & H) H' % (BPCP_kvalid R (ff:=falsity_on)).
apply (H u), (H' D M u).
apply M.

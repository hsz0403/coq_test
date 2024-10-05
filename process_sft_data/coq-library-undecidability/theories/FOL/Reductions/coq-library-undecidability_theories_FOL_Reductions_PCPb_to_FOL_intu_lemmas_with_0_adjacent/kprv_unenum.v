From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.FOL Require Import FOL Util.Kripke Util.Deduction Util.Syntax Util.Tarski PCPb_to_FOL.
From Undecidability.PCP Require Import PCP Reductions.PCPb_iff_dPCPb.
Section kvalidity.
Local Definition BSRS := list (card bool).
Variable R : BSRS.
Context {ff : falsity_flag}.
End kvalidity.

Corollary kprv_unenum : UA -> ~ enumerable (complement (@prv _ _ falsity_on intu nil)).
Proof.
intros H.
apply (not_coenumerable kprv_red); trivial.

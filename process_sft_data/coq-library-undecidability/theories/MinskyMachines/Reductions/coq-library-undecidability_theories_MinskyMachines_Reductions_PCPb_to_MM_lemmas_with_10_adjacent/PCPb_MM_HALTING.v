Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.PCP Require Import PCP PCPb_iff_iPCPb.
From Undecidability.StackMachines Require Import BSM iPCPb_to_BSM_HALTING.
From Undecidability.MinskyMachines Require Import MM BSM_MM.

Theorem PCPb_MM_HALTS_ON_ZERO : PCPb ⪯ MM_HALTS_ON_ZERO.
Proof.
eapply reduces_transitive.
exact PCPb_iff_iPCPb.reductionLR.
eapply reduces_transitive.
exact iPCPb_to_BSM_HALTING.
Admitted.

Theorem PCPb_MM_HALTING : PCPb ⪯ MM_HALTING.
Proof.
eapply reduces_transitive.
exact PCPb_iff_iPCPb.reductionLR.
eapply reduces_transitive.
exact iPCPb_to_BSM_HALTING.
apply BSM_MM_HALTING.

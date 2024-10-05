Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.StackMachines.SMN.
Require Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.
Require Import Undecidability.CounterMachines.CM1_undec.

Theorem SMNdl_UB_undec : undecidable SMNdl_UB.
Proof.
apply (undecidability_from_reducibility CM1_HALT_undec).
exact CM1_HALT_to_SMNdl_UB.reduction.

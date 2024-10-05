Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.MinskyMachines.MM2.
Require Import Undecidability.CounterMachines.CM1.
From Undecidability.CounterMachines.Reductions Require MM2_HALTING_to_CM2_HALT CM2_HALT_to_CM1_HALT.
Theorem reduction : MM2_HALTING ⪯ CM1_HALT.
Proof.
apply (reduces_transitive MM2_HALTING_to_CM2_HALT.reduction).
exact CM2_HALT_to_CM1_HALT.reduction.
Qed.
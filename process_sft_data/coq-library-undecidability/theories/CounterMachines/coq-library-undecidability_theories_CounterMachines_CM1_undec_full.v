Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Reductions.CM2_HALT_to_CM1_HALT.
Require Import Undecidability.CounterMachines.CM2_undec.
Lemma CM1_HALT_undec : undecidable CM1_HALT.
Proof.
apply (undecidability_from_reducibility CM2_HALT_undec).
exact CM2_HALT_to_CM1_HALT.reduction.
Qed.
Check CM1_HALT_undec.
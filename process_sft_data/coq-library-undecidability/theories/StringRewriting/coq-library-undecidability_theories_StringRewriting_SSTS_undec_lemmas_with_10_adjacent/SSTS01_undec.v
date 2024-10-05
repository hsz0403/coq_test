Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.StringRewriting.SSTS.
Require Import Undecidability.CounterMachines.CM2_undec.
Require Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.
Check SSTS01_undec.

Lemma SSTS01_undec : undecidable SSTS01.
Proof.
apply (undecidability_from_reducibility CM2_HALT_undec).
apply CM2_HALT_to_SSTS01.reduction.

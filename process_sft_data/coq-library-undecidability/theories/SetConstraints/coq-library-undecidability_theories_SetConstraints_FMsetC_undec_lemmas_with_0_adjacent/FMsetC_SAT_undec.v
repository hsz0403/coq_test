Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.SetConstraints.FMsetC.
Require Undecidability.SetConstraints.Reductions.H10UC_SAT_to_FMsetC_SAT.
Require Import Undecidability.DiophantineConstraints.H10C_undec.
Check FMsetC_SAT_undec.

Theorem FMsetC_SAT_undec : undecidable FMsetC_SAT.
Proof.
apply (undecidability_from_reducibility H10UC_SAT_undec).
exact H10UC_SAT_to_FMsetC_SAT.reduction.

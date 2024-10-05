Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.DiophantineConstraints.H10C.
From Undecidability.DiophantineConstraints.Reductions Require FRACTRAN_to_H10C_SAT H10C_SAT_to_H10SQC_SAT H10SQC_SAT_to_H10UC_SAT.
From Undecidability.FRACTRAN Require Import FRACTRAN FRACTRAN_undec.

Theorem H10SQC_SAT_undec : undecidable H10SQC_SAT.
Proof.
apply (undecidability_from_reducibility H10C_SAT_undec).
exact H10C_SAT_to_H10SQC_SAT.reduction.

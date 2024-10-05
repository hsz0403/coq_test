Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.DiophantineConstraints.H10C.
From Undecidability.DiophantineConstraints.Reductions Require FRACTRAN_to_H10C_SAT H10C_SAT_to_H10SQC_SAT H10SQC_SAT_to_H10UC_SAT.
From Undecidability.FRACTRAN Require Import FRACTRAN FRACTRAN_undec.

Theorem H10C_SAT_undec : undecidable H10C_SAT.
Proof.
apply (undecidability_from_reducibility FRACTRAN_undec).
apply (reduces_transitive FRACTRAN_DIO.FRACTRAN_HALTING_DIO_LOGIC_SAT).
apply (reduces_transitive FRACTRAN_DIO.DIO_LOGIC_ELEM_SAT).
exact FRACTRAN_to_H10C_SAT.DIO_ELEM_H10C_SAT.

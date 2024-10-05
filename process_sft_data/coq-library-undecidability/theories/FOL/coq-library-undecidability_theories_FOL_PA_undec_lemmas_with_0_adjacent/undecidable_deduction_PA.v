Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.PA.
From Undecidability.H10 Require Import H10p_undec.
From Undecidability.FOL.Reductions Require Import H10p_to_FA.

Theorem undecidable_deduction_PA : undecidable deduction_PA.
Proof.
refine (undecidability_from_reducibility _ H10_to_deduction_PA).
apply H10p_undec.

Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.SemiUnification.SemiU.
Require Undecidability.SemiUnification.Reductions.CSSM_UB_to_SSemiU.
Require Undecidability.SemiUnification.Reductions.SSemiU_to_RU2SemiU.
Require Undecidability.SemiUnification.Reductions.RU2SemiU_to_LU2SemiU.
Require Undecidability.SemiUnification.Reductions.RU2SemiU_to_SemiU.
Require Import Undecidability.StackMachines.SSM_undec.
Check SemiU_undec.

Theorem SSemiU_undec : undecidable SSemiU.
Proof.
apply (undecidability_from_reducibility CSSM_UB_undec).
exact CSSM_UB_to_SSemiU.reduction.

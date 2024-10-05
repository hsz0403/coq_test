Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.StackMachines.SSM.
Require Undecidability.StackMachines.Reductions.SMNdl_UB_to_CSSM_UB.
Require Import Undecidability.StackMachines.SMN_undec.
Theorem CSSM_UB_undec : undecidable CSSM_UB.
Proof.
apply (undecidability_from_reducibility SMNdl_UB_undec).
exact SMNdl_UB_to_CSSM_UB.reduction.
Qed.
Check CSSM_UB_undec.
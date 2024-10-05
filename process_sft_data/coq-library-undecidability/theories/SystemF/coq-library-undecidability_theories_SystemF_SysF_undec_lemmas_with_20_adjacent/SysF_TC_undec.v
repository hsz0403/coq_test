Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.SystemF.SysF.
From Undecidability.SystemF.Reductions Require H10C_SAT_to_SysF_INH LU2SemiU_to_SysF_TYP SysF_TYP_to_SysF_TC.
Require Import Undecidability.DiophantineConstraints.H10C_undec Undecidability.SemiUnification.SemiU_undec.
Check SysF_INH_undec.
Check SysF_TYP_undec.
Check SysF_TC_undec.

Theorem SysF_INH_undec : undecidable SysF_INH.
Proof.
apply (undecidability_from_reducibility H10C_SAT_undec).
Admitted.

Theorem SysF_TYP_undec : undecidable SysF_TYP.
Proof.
apply (undecidability_from_reducibility LU2SemiU_undec).
Admitted.

Theorem SysF_TC_undec : undecidable SysF_TC.
Proof.
apply (undecidability_from_reducibility SysF_TYP_undec).
exact SysF_TYP_to_SysF_TC.reduction.

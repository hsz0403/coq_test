Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.MuRec.RA_UNIV_HALT.
Require Undecidability.MuRec.Reductions.H10C_SAT_to_RA_UNIV_HALT.
Require Import Undecidability.DiophantineConstraints.H10C_undec.
Theorem RA_UNIV_HALT_undec : undecidable RA_UNIV_HALT.
Proof.
apply (undecidability_from_reducibility H10C_SAT_undec).
exact H10C_SAT_to_RA_UNIV_HALT.H10C_SAT_RA_UNIV_HALT.
Qed.
Check RA_UNIV_HALT_undec.
Require Import List.
From Undecidability.MuRec Require Import recalg ra_univ ra_univ_andrej.
Require Import Undecidability.MuRec.RA_UNIV_HALT.
Require Import Undecidability.DiophantineConstraints.H10C.
Require Import Undecidability.Synthetic.Undecidability.
Set Implicit Arguments.
Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).
Definition H10C_RA_UNIV : list h10c -> RA_UNIV_PROBLEM.
Proof.
intros lc.
destruct (nat_h10lc_surj lc) as (k & Hk).
exact k.
Defined.
Check H10C_SAT_RA_UNIV_HALT.
Definition H10UC_RA_UNIV_AD : list h10uc -> RA_UNIV_PROBLEM.
Proof.
intros lc.
destruct (nat_h10luc_surj lc) as (k & Hk).
exact k.
Defined.
Check H10UC_SAT_RA_UNIV_AD_HALT.

Definition H10UC_RA_UNIV_AD : list h10uc -> RA_UNIV_PROBLEM.
Proof.
intros lc.
destruct (nat_h10luc_surj lc) as (k & Hk).
exact k.

Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.MinskyMachines Require Import ndMM2 ndMM2_undec.
From Undecidability.ILL Require Import IMSELL ndMM2_IMSELL.
Local Infix "≤" := (@IMSELL_le _) (at level 70).
Local Notation "u ≰ v" := (~ u ≤ v) (at level 70).
Local Notation U := (@IMSELL_U _).
Theorem IMSELL_undec (S : IMSELL_sig3) : undecidable (@IMSELL_cf_PROVABILITY3 S).
Proof.
apply (undecidability_from_reducibility ndMM2_undec).
now apply ndMM2_IMSELL.reduction.
Qed.
Theorem IMSELL3_undec : undecidable (@IMSELL_cf_PROVABILITY imsell3).
Proof.
refine (@IMSELL_undec (exist _ imsell3 _)).
now exists (Some true), (Some false), None.
Qed.
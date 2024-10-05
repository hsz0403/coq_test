Require Import List.
From Undecidability.Shared.Libs.DLW.Vec Require Import vec.
From Undecidability.MuRec Require Import recalg ra_univ ra_univ_andrej.
Set Implicit Arguments.
Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).
Definition RA_UNIV_PROBLEM := nat.
Definition RA_UNIV_HALT (n : RA_UNIV_PROBLEM) : Prop := ex (⟦ra_univ⟧ (n##vec_nil)).
Definition RA_UNIV_AD_HALT (n : RA_UNIV_PROBLEM) : Prop := ex (⟦ra_univ_ad⟧ (n##vec_nil)).
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Shared.Libs.DLW Require Import pos vec sss.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MuRec Require Import recalg ra_simul.
Set Default Proof Using "Type".
Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).
Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity).
Section MUREC_MM_HALTING.
Let f : MUREC_PROBLEM -> MM_PROBLEM.
Proof.
intros g.
destruct (ra_mm_simulator g) as (m & P & _).
exists (S m), P; apply vec_zero.
Defined.
End MUREC_MM_HALTING.

Let f : MUREC_PROBLEM -> MM_PROBLEM.
Proof.
intros g.
destruct (ra_mm_simulator g) as (m & P & _).
exists (S m), P; apply vec_zero.

Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils_tac utils_nat pos vec sss.
From Undecidability.MinskyMachines Require Import mm_defs.
From Undecidability.MuRec Require Import recalg ra_mm.
Set Implicit Arguments.
Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).
Local Notation "P // s -+> t" := (sss_progress (@mm_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mm_sss _) P s t).
Local Notation "P // s ~~> t" := (sss_output (@mm_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@mm_sss _) P s).

Theorem ra_mm_simulator n (f : recalg n) : { m & { P : list (mm_instr (pos (n+S m))) | forall v, ex (⟦f⟧ v) <-> (1,P) // (1,vec_app v vec_zero) ↓ } }.
Proof.
destruct (ra_mm_compiler f) as (m & P & H1 & H2).
exists m, P; split.
+
intros (x & Hx).
exists (1+length P,vec_app v (x##vec_zero)); split; auto.
simpl; lia.
+
intros H; apply H2; eq goal H; do 2 f_equal.

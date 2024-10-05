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

Corollary ra_mm_simulator_0 (f : recalg 0) : { m & { P : list (mm_instr (pos (S m))) | ex (⟦f⟧ vec_nil) <-> (1,P) // (1,vec_zero) ↓ } }.
Proof.
destruct (ra_mm_simulator f) as (m & P & HP).
exists m, P; rewrite (HP vec_nil), vec_app_nil; tauto.

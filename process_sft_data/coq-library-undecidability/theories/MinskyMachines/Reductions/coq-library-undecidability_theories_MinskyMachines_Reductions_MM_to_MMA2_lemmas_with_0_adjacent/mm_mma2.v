Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Shared.Libs.DLW Require Import Utils.utils Vec.pos Vec.vec.
From Undecidability.Shared.Libs.DLW.Code Require Import sss.
From Undecidability.MinskyMachines Require Import MM FRACTRAN_to_MMA2.
From Undecidability.FRACTRAN Require Import FRACTRAN MM_FRACTRAN.
Set Implicit Arguments.
Check MM_MMA2_HALTING.
From Undecidability.MinskyMachines Require Import mm_defs mma_defs fractran_mma.
From Undecidability.FRACTRAN Require Import fractran_utils prime_seq mm_fractran.
Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity).
Local Notation "P /MMA/ s ↓" := (sss_terminates (@mma_sss 2) P s) (at level 70, no associativity).

Theorem mm_mma2 n (P : list (mm_instr (pos n))) : { Q : list (mm_instr (pos 2)) & { f : vec nat n -> vec nat 2 | forall v, (1,P) /MM/ (1,v) ↓ <-> (1,Q) /MMA/ (1,f v) ↓ } }.
Proof.
destruct (mm_fractran_not_zero P) as (l & H1 & H2).
exists (fractran_mma l), (fun v => ps 1 * exp 1 v ## 0 ## vec_nil).
intros v; rewrite H2.
apply fractran_mma_reduction; trivial.
revert H1; apply Forall_impl; tauto.

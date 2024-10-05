Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Shared.Libs.DLW Require Import utils list_bool pos vec subcode sss.
From Undecidability.StackMachines Require Import bsm_defs.
From Undecidability.MinskyMachines.MM Require Import mm_defs mm_utils mm_comp.
Set Default Proof Using "Type".
Local Notation "P '/BSM/' s ↓" := (sss_terminates (@bsm_sss _) P s) (at level 70, no associativity).
Local Notation "P '/MM/' s ~~> t" := (sss_output (@mm_sss _) P s t) (at level 70, no associativity).
Section BSM_MM_HALTS_ON_ZERO.
Let f : BSM_PROBLEM -> MM_PROBLEM.
Proof.
intros (n & i & P & v).
destruct (bsm_mm_compiler_2 i P) as (Q & _).
exists (2+n), Q.
exact (0##0##vec_map stack_enc v).
Defined.
End BSM_MM_HALTS_ON_ZERO.
Section BSM_MM_HALTING.
Let f : BSM_PROBLEM -> MM_PROBLEM.
Proof.
intros (n & i & P & v).
destruct (bsm_mm_compiler_1 i P) as (Q & _).
exists (2+n), Q.
exact (0##0##vec_map stack_enc v).
Defined.
End BSM_MM_HALTING.

Let f : BSM_PROBLEM -> MM_PROBLEM.
Proof.
intros (n & i & P & v).
destruct (bsm_mm_compiler_1 i P) as (Q & _).
exists (2+n), Q.
exact (0##0##vec_map stack_enc v).

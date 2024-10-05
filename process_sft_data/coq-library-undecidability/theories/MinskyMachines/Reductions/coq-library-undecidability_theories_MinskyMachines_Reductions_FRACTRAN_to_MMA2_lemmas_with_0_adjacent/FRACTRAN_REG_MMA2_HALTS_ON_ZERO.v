Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Shared.Libs.DLW Require Import pos vec sss.
From Undecidability.FRACTRAN Require Import FRACTRAN.
From Undecidability.MinskyMachines Require Import mma_defs fractran_mma.
Set Implicit Arguments.
Set Default Proof Using "Type".
Local Notation "P //ₐ s ↓" := (sss_terminates (@mma_sss 2) P s) (at level 70, no associativity).
Section FRACTRAN_REG_MMA2_and_ON_ZERO.
Let f : FRACTRAN_REG_PROBLEM -> MMA2_PROBLEM.
Proof.
intros (Q & x & _).
exact (fractran_mma0 Q,x##0##vec_nil).
Defined.
End FRACTRAN_REG_MMA2_and_ON_ZERO.
Check FRACTRAN_REG_MMA2_HALTING.
Check FRACTRAN_REG_MMA2_HALTS_ON_ZERO.

Theorem FRACTRAN_REG_MMA2_HALTS_ON_ZERO : FRACTRAN_REG_HALTING ⪯ MMA2_HALTS_ON_ZERO.
Proof.
exists f; intros (? & ? & ?); simpl.
now apply fractran_reg_mma0_reductions.

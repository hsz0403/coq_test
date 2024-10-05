Require Import List Arith Relations Lia.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec sss subcode.
From Undecidability.MinskyMachines Require Import mma_defs mma_simul.
Set Implicit Arguments.

Theorem MMA2_MMA2_HALTS_ON_ZERO : MMA2_HALTING ⪯ MMA2_HALTS_ON_ZERO.
Proof.
apply reduces_dependent; exists.
intros (P,v).
destruct mma2_simulator with 1 P as (Q & HQ).
exists (Q,v); apply HQ.

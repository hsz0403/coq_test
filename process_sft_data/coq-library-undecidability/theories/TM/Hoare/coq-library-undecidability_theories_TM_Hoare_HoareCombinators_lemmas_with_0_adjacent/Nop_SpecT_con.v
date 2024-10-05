From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma Nop_SpecT_con (sig : finType) (n : nat) (P : Assert sig n) k : TripleT P k Nop (fun _ => P).
Proof.
eapply ConsequenceT_pre.
-
apply Nop_SpecT.
-
auto.
-
lia.

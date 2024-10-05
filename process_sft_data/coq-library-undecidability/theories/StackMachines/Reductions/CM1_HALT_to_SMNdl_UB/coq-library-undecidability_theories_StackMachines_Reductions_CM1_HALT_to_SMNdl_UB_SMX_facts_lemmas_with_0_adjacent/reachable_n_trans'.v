Require Import List Lia Relation_Operators.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.SMX.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Section SMX_facts.
Context {State Symbol : Set}.
Local Definition Config := @Config State Symbol.
Inductive reachable_n (M: SMX) : nat -> Config -> Config -> Prop := | reach_refl (n: nat) (X: Config) : reachable_n M n X X | reach_step (n: nat) (X Y Z: Config) : step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.
Definition terminal (M: SMX) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Definition maybe_reachable (M: SMX) (n: nat) (X Y: Config) : Prop := reachable_n M n X Y \/ (exists Z, reachable_n M n X Z /\ terminal M Z).
End SMX_facts.

Lemma reachable_n_trans' {M} n {m k X X' Y Z} : m+n <= k -> X = X' -> reachable_n M n Y Z -> reachable_n M m X Y -> reachable_n M k X' Z.
Proof.
move /reachable_n_mon => H *.
subst.
apply: H.
by apply: reachable_n_trans; eassumption.

Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma reachable_stack_app {M l r x l' r' y v w} : reachable M (l, r, x) (l', r', y) -> reachable M (l ++ v, r ++ w, x) (l' ++ v, r' ++ w, y).
Proof.
move /reachable_to_reachable_n => [?] /reachable_n_stack_app ?.
by apply: reachable_n_to_reachable.

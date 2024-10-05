Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma reachable_to_reachable_n {M X Y} : reachable M X Y -> exists n, reachable_n M n X Y.
Proof.
move /rt_rt1n.
elim; first by (move=> ?; exists 0; apply: rn_refl).
move=> > ? _ [n ?].
exists (1+n).
apply: rn_step; by eassumption.

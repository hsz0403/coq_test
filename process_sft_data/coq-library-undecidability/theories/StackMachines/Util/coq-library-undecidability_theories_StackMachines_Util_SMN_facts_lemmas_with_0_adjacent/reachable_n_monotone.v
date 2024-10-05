Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma reachable_n_monotone {M X Y m n} : m <= n -> reachable_n M m X Y -> reachable_n M n X Y.
Proof.
elim: n m X Y.
{
move=> m > ?.
have ->: m = 0 by lia.
move /reachable_0E => ->.
by apply: rn_refl.
}
move=> n IH [|m] > ?.
{
move /reachable_0E => ->.
by apply: rn_refl.
}
move /reachable_SnE => [-> | [Z [? ?]]]; first by apply: rn_refl.
apply: rn_step; first by eassumption.
apply: IH; last by eassumption.
by lia.

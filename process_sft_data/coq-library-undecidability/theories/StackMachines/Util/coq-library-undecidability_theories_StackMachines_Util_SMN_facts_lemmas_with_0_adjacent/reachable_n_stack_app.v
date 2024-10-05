Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma reachable_n_stack_app {M n l r x l' r' y v w} : reachable_n M n (l, r, x) (l', r', y) -> reachable_n M n (l ++ v, r ++ w, x) (l' ++ v, r' ++ w, y).
Proof.
elim: n l r x l' r' y.
{
move=> > /reachable_0E [] <- <- <-.
apply: rn_refl.
}
move=> n IH l r x l' r' y /reachable_SnE [[] <- <- <- | [z] [+]]; first by apply: rn_refl.
move Hx': (l, r, x) => x' Hx'z.
case: Hx'z Hx'.
move=> > H [] -> -> -> /IH {}IH.
apply: rn_step; last by eassumption.
rewrite -?app_assoc.
by apply: transition.

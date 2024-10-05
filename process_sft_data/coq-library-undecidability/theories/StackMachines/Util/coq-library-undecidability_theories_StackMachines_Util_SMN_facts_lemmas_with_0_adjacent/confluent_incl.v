Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma confluent_incl {M1 M2} : incl M1 M2 -> incl M2 M1 -> confluent M1 -> confluent M2.
Proof.
move=> /reachable_incl H12 /reachable_incl H21 HM1 ? ? ? /H21 /HM1 {}HM1 /H21 /HM1 [? [? ?]].
eexists.
constructor; apply: H12; by eassumption.

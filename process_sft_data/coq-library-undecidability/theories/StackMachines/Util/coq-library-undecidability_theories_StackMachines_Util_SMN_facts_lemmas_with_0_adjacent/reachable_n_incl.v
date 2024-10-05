Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma reachable_n_incl {M1 M2 n X Y} : incl M1 M2 -> reachable_n M1 n X Y -> reachable_n M2 n X Y.
Proof.
move=> H.
elim: n X Y.
{
move=> > /reachable_0E ->.
by apply: rn_refl.
}
move=> n IH > /reachable_SnE.
case.
-
move=> ->.
by apply: rn_refl.
-
move=> [?] [? ?].
apply: rn_step.
+
apply: step_incl; by eassumption.
+
by apply: IH.

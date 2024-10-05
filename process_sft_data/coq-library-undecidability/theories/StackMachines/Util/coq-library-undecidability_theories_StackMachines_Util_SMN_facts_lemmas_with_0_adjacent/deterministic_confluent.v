Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma deterministic_confluent {M} : deterministic M -> confluent M.
Proof.
move=> HM ? ? + /rt_rt1n Hxy1.
elim: Hxy1.
{
move=> *.
eexists.
by constructor; last by apply: rt_refl.
}
move=> ? ? ? Hxy1 /rt_rt1n Hy1z1 IH ? /rt_rt1n Hxy2.
case: Hxy2 Hxy1.
-
move=> ?.
eexists.
constructor; first by apply: rt_refl.
apply: rt_trans; last by eassumption.
apply: rt_step.
by eassumption.
-
move=> > Hxy2 /rt_rt1n Hy2z2 Hxy1.
have ? := HM _ _ _ Hxy1 Hxy2.
subst.
by apply: IH.

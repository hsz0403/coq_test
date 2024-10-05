Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma concat_reachable {M} {NM: nat} (xs : list Config) : bounded M NM -> exists L, (forall x y, In x xs -> reachable M x y -> In y L) /\ length L <= NM * length xs.
Proof.
move=> bounded_M.
elim: xs.
{
exists [].
constructor; [done | by (move=> /=; lia) ].
}
move=> x xs [Lxs [HLxs ?]].
have [Lx [HLx ?]] := bounded_M x.
exists (Lx ++ Lxs).
constructor; last by (rewrite app_length /=; lia).
move=> ? ? /=.
rewrite in_app_iff.
case.
-
move=> <- /HLx *.
by left.
-
move=> *.
right.
apply: HLxs; by eassumption.

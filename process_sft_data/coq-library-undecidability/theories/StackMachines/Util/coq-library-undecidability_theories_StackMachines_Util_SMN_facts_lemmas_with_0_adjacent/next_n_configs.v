Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma next_n_configs M (n: nat) (Xs: list Config) : exists L, (forall X Y, In X Xs -> reachable_n M n X Y -> In Y L) /\ (length L <= (Nat.pow (1 + length M) n) * length Xs * (1+n)).
Proof.
elim: n Xs.
-
move=> Xs.
exists Xs.
constructor; last by (move=> /=; lia).
by move=> X Y ? => /reachable_0E => <-.
-
move=> n IH Xs.
have [Ys [HYs ?]]: exists L, (forall X Y, In X Xs -> step M X Y -> In Y L) /\ length L <= (1 + length M) * length Xs.
{
clear.
elim: Xs.
{
exists [].
constructor; [done | by move=> /=; lia].
}
move=> X Xs [L [HL ?]].
have [LX [HLX ?]] := next_configs M X.
exists (LX ++ L).
constructor; first last.
-
rewrite app_length /length -?/(length _).
by lia.
-
move=> > /=.
rewrite in_app_iff.
move=> [<- /HLX ? | * ]; first by left.
right.
apply: HL; by eassumption.
}
have [L [HL ?]] := IH Ys.
exists (Xs ++ L).
constructor.
{
move=> X Y HX /reachable_SnE.
case.
-
move=> <-.
apply /in_app_iff.
by left.
-
move=> [Z] [/HYs] /(_ HX) /HL => H /H ?.
apply /in_app_iff.
by right.
}
rewrite app_length.
suff: length L <= (1 + length M) ^ S n * length Xs * (1 + n).
{
have := Nat.pow_nonzero (1 + length M) (S n) ltac:(lia).
by nia.
}
rewrite /Nat.pow -/Nat.pow.
have ? := Nat.pow_nonzero (1 + length M) n ltac:(lia).
suff: (1 + length M) ^ n * length Ys <= (1 + length M) * (1 + length M) ^ n * length Xs by nia.
by nia.

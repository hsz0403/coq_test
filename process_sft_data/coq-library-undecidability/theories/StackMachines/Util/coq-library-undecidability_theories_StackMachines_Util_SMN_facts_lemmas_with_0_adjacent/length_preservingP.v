Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma length_preservingP {M l r x l' r' y} : length_preserving M -> reachable M (l, r, x) (l', r', y) -> (l, r, x) = (l', r', y) \/ (length (l ++ r) = length (l' ++ r') /\ 1 <= length (l ++ r)).
Proof.
move=> HM /reachable_to_reachable_n [n].
elim: n l r x l' r' y.
{
move=> > /reachable_0E => ?.
by left.
}
move=> n IH l r x l' r' y /reachable_SnE [? | [Z] []]; first by left.
move HX: (l, r, x) => X HXZ.
case: HXZ HX.
move=> > /HM [].
rewrite ?app_length.
move=> ? ? [] ? ? ?.
subst.
move /IH.
case.
-
move=> [] *.
subst.
rewrite ?app_length.
right.
by lia.
-
rewrite ?app_length.
move=> [] ? ?.
right.
by lia.

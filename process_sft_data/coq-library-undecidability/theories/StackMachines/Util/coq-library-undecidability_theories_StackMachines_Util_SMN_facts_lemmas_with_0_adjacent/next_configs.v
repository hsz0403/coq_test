Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma next_configs M (X: Config) : exists L, (forall Y, step M X Y -> In Y L) /\ length L <= length M.
Proof.
elim: M.
{
exists [].
constructor=> > /=; [by case | by lia].
}
move: X => [[lx rx] x] [[[l r] y] [[l' r'] z]] M [L [HL ?]].
have [[] * | Hy] : (firstn (length l) lx, firstn (length r) rx, x) = (l, r, y) \/ (firstn (length l) lx, firstn (length r) rx, x) <> (l, r, y) by do 4 decide equality.
-
exists ((l' ++ skipn (length l) lx, r' ++ skipn (length r) rx, z) :: L).
constructor; last by (move=> /=; lia).
move HX: (lx, rx, x) => X Z HXZ.
case: HXZ HX => v w > /=.
case.
+
move=> + [] => [[]] *.
subst.
left.
by rewrite ?skipn_app ?skipn_all ?Nat.sub_diag /=.
+
move /transition => /(_ v w) ? ?.
right.
apply: HL.
by congruence.
-
exists L.
constructor; last by (move=> /=; lia).
move HX: (lx, rx, x) => X Z HXZ.
case: HXZ HX => v w > /=.
case.
+
move=> + [] => [[]] *.
subst.
exfalso.
apply: Hy.
by rewrite ?firstn_app ?firstn_all ?Nat.sub_diag ?app_nil_r.
+
move /transition => /(_ v w) ? ?.
apply: HL.
by congruence.

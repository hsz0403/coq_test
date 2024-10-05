Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Definition terminal (M: SMN) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop := | rn_refl n X : reachable_n M n X X | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma stepI {M: SMN} {X Y: Config} v w l r l' r' x y : X = (l ++ v, r ++ w, x) -> Y = (l' ++ v, r' ++ w, y) -> In ((l, r, x), (l', r', y)) M -> step M X Y.
Proof.
move=> -> -> /transition.
Admitted.

Lemma step_incl {M1 M2 X Y} : incl M1 M2 -> step M1 X Y -> step M2 X Y.
Proof.
move=> HM1M2.
case=> > /HM1M2.
Admitted.

Lemma reachable_0E {M X Y} : reachable_n M 0 X Y -> X = Y.
Proof.
move Hn: (0) => n HXY.
case: HXY Hn; first done.
Admitted.

Lemma reachable_SnE {M n X Z} : reachable_n M (1+n) X Z -> X = Z \/ (exists Y, step M X Y /\ reachable_n M n Y Z).
Proof.
move Hn': (1+n) => n' HXY.
case: HXY Hn'; first by (move=> *; left).
move=> {}n' *.
right.
have ->: n = n' by lia.
Admitted.

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
Admitted.

Lemma reachable_to_reachable_n {M X Y} : reachable M X Y -> exists n, reachable_n M n X Y.
Proof.
move /rt_rt1n.
elim; first by (move=> ?; exists 0; apply: rn_refl).
move=> > ? _ [n ?].
exists (1+n).
Admitted.

Lemma reachable_n_to_reachable {M n X Y} : reachable_n M n X Y -> reachable M X Y.
Proof.
elim; first by (move=> *; apply: rt_refl).
move=> *.
apply: rt_trans; last by eassumption.
Admitted.

Lemma reachable_incl {M1 M2 X Y} : incl M1 M2 -> reachable M1 X Y -> reachable M2 X Y.
Proof.
move=> /reachable_n_incl H /reachable_to_reachable_n [?] ?.
apply: reachable_n_to_reachable.
apply: H.
Admitted.

Lemma confluent_incl {M1 M2} : incl M1 M2 -> incl M2 M1 -> confluent M1 -> confluent M2.
Proof.
move=> /reachable_incl H12 /reachable_incl H21 HM1 ? ? ? /H21 /HM1 {}HM1 /H21 /HM1 [? [? ?]].
eexists.
Admitted.

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
Admitted.

Lemma step_app {M1 M2 x y} : step (M1 ++ M2) x y -> step M1 x y \/ step M2 x y.
Proof.
case=> >.
rewrite in_app_iff.
Admitted.

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
Admitted.

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

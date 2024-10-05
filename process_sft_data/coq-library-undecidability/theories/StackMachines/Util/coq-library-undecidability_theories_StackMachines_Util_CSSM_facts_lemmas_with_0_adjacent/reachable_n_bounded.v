Require Import PeanoNat Lia Relation_Operators Operators_Properties List.
Import ListNotations.
Require Import ssreflect ssrfun ssrbool.
Require Import Undecidability.StackMachines.SSM.
From Undecidability.StackMachines.Util Require Import Facts.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Definition width : config -> nat := fun '(A, B, _) => length A + length B.
Section CSSM.
Context {M : ssm}.
Variable confluent_M : confluent M.
Arguments confluent_M {X Y1 Y2}.
Definition equiv (X Y: config) := exists (Z: config), reachable M X Z /\ reachable M Y Z.
Fixpoint enum_stacks (n: nat) : list stack := if n is S n then (map (cons true) (enum_stacks n)) ++ (map (cons false) (enum_stacks n)) else [[]].
Fixpoint enum_states (M': ssm) : list state := match M' with | [] => [] | (x, y, _, _, _) :: M' => x :: y :: enum_states M' end.
Definition get_state : config -> state := fun '(_, _, x) => x.
Definition enum_configs (lA lB: nat) : list config := list_prod (list_prod (enum_stacks lA) (enum_stacks lB)) (enum_states M).
Definition space (X: config) : list config := X :: flat_map (fun i => enum_configs i (width X - i)) (seq 0 (width X + 1)).
Definition get_left : config -> stack := fun '(A, _, _) => A.
Definition get_right : config -> stack := fun '(_, B, _) => B.
Inductive reachable_n : nat -> config -> config -> Prop := | rn_refl n X : reachable_n n X X | rn_step n X Y Z: reachable_n n X Y -> step M Y Z -> reachable_n (1+n) X Z.
Definition narrow (X: config) := exists (x: state) (A: stack), equiv X (A, [], x).
Definition bounded' (n: nat) : Prop := forall (c: config) (x y: state) (A B: stack), reachable M (A, [], x) c -> reachable M ([], B, y) c -> length B <= n.
End CSSM.

Lemma reachable_n_bounded {X Y: config} {n: nat} {L: list config} : (forall Z, reachable_n n X Z -> In Z L) -> reachable_n n X Y -> reachable_n (length L) X Y.
Proof.
elim /(measure_ind id): n L X Y.
case.
{
move=> /= *.
apply: reachable_n_monotone; last by eassumption.
by lia.
}
move=> n IH L X Y HL.
case: (reachable_n_dec n X Y) => HXY.
{
move=> _.
apply: (IH n ltac:(lia)); last by eassumption.
move=> ? ?.
apply: HL.
apply: reachable_n_monotone; last by eassumption.
by lia.
}
move=> H'XY.
have := HL _ H'XY.
move /(@in_split config) => [L1 [L2 ?]].
subst L.
move: H'XY => /reachable_SnE.
case.
{
move=> ->.
by apply: rn_refl.
}
move=> [Z [HXZ HZY]].
rewrite ?app_length /length -?/(length _).
have ->: (length L1 + S (length L2)) = 1 + length (L1 ++ L2) by rewrite app_length; lia.
apply: rn_step; last by eassumption.
apply: (IH n ltac:(lia)); last by eassumption.
move=> Z' HXZ'.
have HYZ' : Y <> Z' by move=> ?; subst.
move: HXZ' HYZ' => /reachable_n_monotone => /(_ (1+n) ltac:(lia)) /HL.
rewrite ?in_app_iff /In -?/(In _ _).
clear.
by firstorder done.

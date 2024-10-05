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

Lemma bounded_stack_difference {n: nat} {x y: state} {A B C D: stack} : bounded M n -> reachable M (A, B, x) (C, D, y) -> length B <= length D + n /\ length D <= length B + n.
Proof.
move /(_ (A, B, x)) => [L [HL1 HL2]].
move /reachable_to_reachable_n => [m].
move /(reachable_n_bounded (L := L)).
apply: unnest.
{
move=> *.
apply: HL1.
apply: reachable_n_to_reachable.
by eassumption.
}
move /reachable_n_monotone => /(_ n ltac:(lia)).
clear m HL1 HL2 L.
elim: n x y A B C D.
{
move=> > /reachable_0E [] *.
subst.
by lia.
}
move=> n IH x y A B C D /reachable_SnE.
case.
{
move=> [] *.
subst.
by lia.
}
move=> [[[C' D'] z]] [/IH] {}IH.
move HZ: (C', D', z) => Z.
move HY: (C, D, y) => Y HZY.
case: HZY HZ HY.
-
move=> > _ [] ? ? ? [] ? ? ?.
subst.
move: IH.
rewrite /length -?/(length _).
by lia.
-
move=> > _ [] ? ? ? [] ? ? ?.
subst.
move: IH.
rewrite /length -?/(length _).
by lia.

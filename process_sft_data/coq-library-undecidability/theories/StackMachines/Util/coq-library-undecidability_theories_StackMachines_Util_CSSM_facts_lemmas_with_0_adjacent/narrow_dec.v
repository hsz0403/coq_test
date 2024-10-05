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

Lemma narrow_dec (X: config) : decidable (narrow X).
Proof.
case: (Exists_dec (fun Y => get_right Y = [] /\ equiv X Y) (space X)).
-
move=> [[A + ] y].
case; first last.
{
move=> >.
right.
by move=> [+].
}
case: (equiv_dec X (A, [], y)).
+
move=> ?.
by left.
+
move=> ?.
right.
by move=> [_].
-
move=> + /ltac:(left).
rewrite Exists_exists.
move=> [[[A B] y] [_]] /= [->] ?.
by exists y, A.
-
move=> + /ltac:(right) => + [y [A HX]].
rewrite Exists_exists.
apply.
exists (A, [], y).
constructor; last done.
by apply: space_equivP.

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

Theorem reachable_suffixes (X: config) : (exists A x y B, reachable M X (A, [], x) /\ reachable M X ([], B, y)) \/ (exists AX a, get_left X = AX ++ [a] /\ forall Y, reachable M X Y -> exists AY, get_left Y = AY ++ [a] /\ reachable M (AX, get_right X, get_state X) (AY, get_right Y, get_state Y)) \/ (exists BX b, get_right X = BX ++ [b] /\ forall Y, reachable M X Y -> exists BY, get_right Y = BY ++ [b] /\ reachable M (get_left X, BX, get_state X) (get_left Y, BY, get_state Y)).
Proof.
case: (Exists_dec (fun Y => get_right Y = [] /\ reachable M X Y) (space X)).
{
move=> [[A +] x].
case; first last.
-
move=> >.
right.
by move => [? ?].
-
case: (reachable_dec X (A, [], x)); first last.
+
move=> >.
right.
by move => [? ?].
+
move=> ?.
by left.
}
1: case: (Exists_dec (fun Y => get_left Y = [] /\ reachable M X Y) (space X)).
{
move=> [[+ B] x].
case; first last.
-
move=> >.
right.
by move => [? ?].
-
case: (reachable_dec X ([], B, x)); first last.
+
move=> >.
right.
by move => [? ?].
+
move=> ?.
by left.
}
all: rewrite ?Exists_exists.
-
move=> [[[A1 B1] x1]] + [[[A2 B2] x2]] => /= [[_ [? ?]]] [_ [? ?]].
subst.
left.
do 4 eexists.
constructor; by eassumption.
-
move=> HX _.
right.
left.
case: (stack_eq_dec (get_left X) []).
{
move=> ?.
exfalso.
apply: HX.
exists X.
constructor; first by left.
constructor; first done.
apply: rt_refl.
}
move /exists_last => [A [a HAa]].
exists A, a.
constructor; first done.
move=> Y.
move: X HX HAa => [[AX BX] xX] HX /= HAa.
subst.
case /remove_rendundant_suffixL; last done.
move=> [x' [B' ?]].
exfalso.
apply: HX.
exists ([], B', x').
constructor; first by apply: spaceP0.
by constructor.
-
move=> HX.
right.
right.
case: (stack_eq_dec (get_right X) []).
{
move=> ?.
exfalso.
apply: HX.
exists X.
constructor; first by left.
constructor; first done.
apply: rt_refl.
}
move /exists_last => [B [b HBb]].
exists B, b.
constructor; first done.
move=> Y.
move: X HX HBb => [[AX BX] xX] HX /= HBb.
subst.
case /remove_rendundant_suffixR; last done.
move=> [x' [A' ?]].
exfalso.
apply: HX.
exists (A', [], x').
constructor; first by apply: spaceP0.
by constructor.

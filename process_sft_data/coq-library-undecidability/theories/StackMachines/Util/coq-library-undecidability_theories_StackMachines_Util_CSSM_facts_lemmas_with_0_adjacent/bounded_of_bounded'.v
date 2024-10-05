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

Lemma bounded_of_bounded' {n: nat}: bounded' n -> exists (m: nat), bounded M m.
Proof using confluent_M.
move=> Hn.
pose W := (repeat false n, repeat false n, 0) : config.
exists (length (space W)).
elim /(measure_ind width).
move=> X IH.
case: (reachable_suffixes X); last case.
-
move=> [?] [?] [?] [?] [+ /copy] => /confluent_M H [/H{H}] [Y].
move=> [/Hn] H /H{H} ? /reachable_width HwX.
move=> /= in HwX.
exists (space X).
constructor.
+
by move=> ? /spaceP0.
+
apply: space_length => /=.
rewrite repeat_length.
by lia.
-
move: X IH => [[A B] x] IH.
move=> [AX] [a] [HA HX].
move=> /= in HA.
subst.
case: (IH (AX, B, x)).
{
move=> /=.
rewrite app_length /length.
by lia.
}
move=> L [HL1 HL2].
exists (map (fun '(A, B, x) => (A ++ [a], B, x)) L).
constructor; last by rewrite map_length.
move=> [[A' y] B'] /HX [AY] /= [->] /HL1 ?.
rewrite in_map_iff.
eexists.
by constructor; last by eassumption.
-
move: X IH => [[A B] x] IH.
move=> [BX] [b] [HB HX].
move=> /= in HB.
subst.
case: (IH (A, BX, x)).
{
move=> /=.
rewrite app_length /length.
by lia.
}
move=> L [HL1 HL2].
exists (map (fun '(A, B, x) => (A, B ++ [b], x)) L).
constructor; last by rewrite map_length.
move=> [[A' y] B'] /HX [BY] /= [->] /HL1 ?.
rewrite in_map_iff.
eexists.
by constructor; last by eassumption.

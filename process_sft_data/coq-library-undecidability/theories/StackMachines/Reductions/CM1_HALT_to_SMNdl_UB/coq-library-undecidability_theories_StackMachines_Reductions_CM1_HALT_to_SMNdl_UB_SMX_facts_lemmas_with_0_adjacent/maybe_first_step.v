Require Import List Lia Relation_Operators.
Import ListNotations.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.SMX.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Section SMX_facts.
Context {State Symbol : Set}.
Local Definition Config := @Config State Symbol.
Inductive reachable_n (M: SMX) : nat -> Config -> Config -> Prop := | reach_refl (n: nat) (X: Config) : reachable_n M n X X | reach_step (n: nat) (X Y Z: Config) : step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.
Definition terminal (M: SMX) (X: Config) : Prop := forall (Y: Config), not (step M X Y).
Definition maybe_reachable (M: SMX) (n: nat) (X Y: Config) : Prop := reachable_n M n X Y \/ (exists Z, reachable_n M n X Z /\ terminal M Z).
End SMX_facts.

Lemma maybe_first_step {M} (op : Instruction) (v w: list Symbol) {n X Z} : 1 <= n -> In op M -> let '((r, s, x), (r', s', y), b) := op in X = (r ++ v, s ++ w, x) -> maybe_reachable M (n-1) (if b is true then (s' ++ w, r' ++ v, y) else (r' ++ v, s' ++ w, y)) Z -> maybe_reachable M n X Z.
Proof.
move=> Hn.
move: op=> [[[[r s] x] [[r' s'] y]] b].
move /(transition M v w) /reachable_n_step => HXY ? HYZ.
subst X.
move: HYZ => [? | [Z' [HZ' ?]]].
-
left.
move: HXY.
by (apply: (reachable_n_trans' (n-1)); first by lia).
-
right.
exists Z'.
constructor; last done.
move: HXY.
by (apply: (reachable_n_trans' (n-1)); first by lia).

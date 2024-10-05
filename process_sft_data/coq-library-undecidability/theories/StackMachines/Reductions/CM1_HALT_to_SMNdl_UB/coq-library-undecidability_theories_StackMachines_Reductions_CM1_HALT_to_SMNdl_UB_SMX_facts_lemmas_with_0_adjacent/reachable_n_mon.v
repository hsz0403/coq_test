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

Lemma reachable_n_mon {M n m X Y} : n <= m -> reachable_n M n X Y -> reachable_n M m X Y.
Proof.
elim: n m X Y.
{
move=> m X Y ?.
move Hn: (0) => n HXY.
case: HXY Hn => *; [by apply: reach_refl | by lia].
}
move=> n IH m X Y Hnm.
move Hn': (S n) => n' HXY.
case: HXY Hn' => [|{}n'] *; first by apply: reach_refl.
have ->: m = S (m - 1) by lia.
apply: reach_step; first by eassumption.
apply: IH; first by lia.
by (have ->: n = n' by lia).

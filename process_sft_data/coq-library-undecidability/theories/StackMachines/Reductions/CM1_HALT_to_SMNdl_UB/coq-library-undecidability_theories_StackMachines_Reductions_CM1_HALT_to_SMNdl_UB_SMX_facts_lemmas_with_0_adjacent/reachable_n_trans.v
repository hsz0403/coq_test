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

Lemma reachable_n_trans {M} n m X Y Z : reachable_n M n X Y -> reachable_n M m Y Z -> reachable_n M (n+m) X Z.
Proof.
elim: n X Y.
{
move=> X Y /=.
move Hn: (0) => n HXY.
case: HXY Hn; [done | by lia].
}
move=> n IH X Y /=.
move Hn': (S n) => n' HXY.
case: HXY Hn' => [| {}n' {}X Y1 Y2] *.
{
apply: reachable_n_mon; last by eassumption.
by lia.
}
have ?: n' = n by lia.
subst n'.
apply: reach_step; first by eassumption.
by apply: IH; eassumption.

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

Lemma reachable_n_reachable {M T x y} : reachable_n M T x y -> reachable M x y.
Proof.
elim: T x y.
{
move HT: (0) => T x y Hxy.
case: Hxy HT => *; [by apply: rt_refl | by lia].
}
move=> T IH x y.
move HT': (S T) => T' Hxy.
case: Hxy HT'; first by (move=> *; apply: rt_refl).
move=> {}T' {}x z {}y /(@rt_step Config) Hxz + ?.
have ->: T' = T by lia.
move /IH.
by apply: rt_trans.

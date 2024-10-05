Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma in_split_rest {X: Type} {x y: X} {L1 L2: list X} : In y (L1 ++ x :: L2) -> x <> y -> In y (L1 ++ L2).
Proof.
rewrite ?in_app_iff /=.
by firstorder done.

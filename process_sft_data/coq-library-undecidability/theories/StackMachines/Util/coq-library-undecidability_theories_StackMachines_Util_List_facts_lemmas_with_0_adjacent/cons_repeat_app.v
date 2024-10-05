Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma cons_repeat_app {X: Type} {x: X} {xs: list X} {m: nat} : x :: (repeat x m ++ xs) = (repeat x (m+1) ++ xs).
Proof.
by have ->: m + 1 = S m by lia.

Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma repeat_app_appP {X: Type} {x: X} {xs: list X} {n m: nat} : repeat x n ++ (repeat x m ++ xs) = repeat x (n+m) ++ xs.
Proof.
by rewrite -repeat_appP app_assoc.

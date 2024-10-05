Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma app_repeat_cons {X: Type} {n: nat} {x: X} {l: list X} : repeat x (1+n) ++ l = x :: (repeat x n ++ l).
Proof.
done.

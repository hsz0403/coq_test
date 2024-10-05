Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition config_weight (M: Cm1) : Config -> nat := fun '{| state := p; value := v |} => p + length M * v.

Lemma halting_monotone {M : Cm1} {x: Config} {n m: nat} : n <= m -> halting M (Nat.iter n (step M) x) -> halting M (Nat.iter m (step M) x).
Proof.
move=> ? ?.
have -> : m = n + (m-n) by lia.
rewrite iter_plus.
elim: (m-n); first done.
move=> * /=.
by congruence.

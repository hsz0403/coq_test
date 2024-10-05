Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition config_weight (M: Cm1) : Config -> nat := fun '{| state := p; value := v |} => p + length M * v.

Lemma step_value_monotone (M : Cm1) (x: Config) : value x <= value (step M x).
Proof.
move: x => [p [|c]] /=; first by lia.
case: (nth_error M p) => /=; last by lia.
move=> [j n].
move Hr: (S c mod (n + 1)) => [|r] /=; last by lia.
have := mod_frac_lt Hr.
move=> /=.
by lia.

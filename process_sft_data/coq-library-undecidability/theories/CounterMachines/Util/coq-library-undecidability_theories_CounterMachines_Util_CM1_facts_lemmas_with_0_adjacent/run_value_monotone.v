Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition config_weight (M: Cm1) : Config -> nat := fun '{| state := p; value := v |} => p + length M * v.

Lemma run_value_monotone (M : Cm1) (x: Config) (n: nat) : value x <= value (Nat.iter n (step M) x).
Proof.
elim: n=> /=; first by lia.
move=> n IH.
have := step_value_monotone M (Nat.iter n (step M) x).
by lia.

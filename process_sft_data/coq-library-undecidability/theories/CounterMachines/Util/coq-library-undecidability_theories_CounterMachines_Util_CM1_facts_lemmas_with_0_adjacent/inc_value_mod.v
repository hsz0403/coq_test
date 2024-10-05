Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition config_weight (M: Cm1) : Config -> nat := fun '{| state := p; value := v |} => p + length M * v.

Lemma inc_value_mod {M : Cm1} {p: Config} : value p < value (step M p) -> exists t, nth_error M (state p) = Some t /\ ((value p) mod ((snd t)+1) = 0).
Proof.
rewrite /step.
move: p => [i [|c]] /=; first by lia.
case: (nth_error M i) => /=; last by lia.
move=> [j n].
move Hr: (S c mod (n + 1)) => [|r] /=; last by lia.
move=> _.
by exists (j, n).

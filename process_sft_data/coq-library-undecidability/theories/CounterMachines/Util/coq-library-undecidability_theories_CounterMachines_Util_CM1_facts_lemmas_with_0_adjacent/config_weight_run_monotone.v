Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition config_weight (M: Cm1) : Config -> nat := fun '{| state := p; value := v |} => p + length M * v.

Lemma config_weight_run_monotone {M: Cm1} {x: Config} {n: nat} : not (halting M (Nat.iter n (step M) x)) -> config_weight M x < config_weight M (Nat.iter (1+n) (step M) x).
Proof.
elim: n; first by move /config_weight_step_monotone.
move=> n IH HSn.
have /IH : not (halting M (Nat.iter n (step M) x)).
{
move=> Hn.
apply: HSn.
move: Hn.
apply: halting_monotone.
by lia.
}
have := config_weight_step_monotone HSn.
move=> /=.
by lia.

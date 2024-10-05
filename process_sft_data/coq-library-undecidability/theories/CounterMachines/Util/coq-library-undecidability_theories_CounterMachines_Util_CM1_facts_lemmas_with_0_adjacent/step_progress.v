Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition config_weight (M: Cm1) : Config -> nat := fun '{| state := p; value := v |} => p + length M * v.

Lemma step_progress (M : Cm1) (x: Config) : state x < length M -> 1 <= value x -> step M x = {| state := 1 + state x; value := value x |} \/ value x < value (step M x).
Proof.
move=> ? ?.
rewrite /step.
have ->: value x = S (value x - 1) by lia.
move Ho: (nth_error M (state x)) => o.
case: o Ho; first last.
{
move /nth_error_None.
by lia.
}
move=> [j n] _.
case H: (S (value x - 1) mod (n + 1)); last by left.
right => /=.
by apply: mod_frac_lt.

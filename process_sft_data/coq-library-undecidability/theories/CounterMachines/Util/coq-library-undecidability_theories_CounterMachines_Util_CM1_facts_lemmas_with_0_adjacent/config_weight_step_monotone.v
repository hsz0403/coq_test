Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition config_weight (M: Cm1) : Config -> nat := fun '{| state := p; value := v |} => p + length M * v.

Lemma config_weight_step_monotone {M: Cm1} {x: Config} : not (halting M x) -> config_weight M x < config_weight M (step M x).
Proof.
move=> Hx.
suff: not (config_weight M (step M x) <= config_weight M x) by lia.
move: x Hx => [p v].
rewrite /config_weight /=.
case: v => [|v].
{
move=> + /ltac:(exfalso).
by apply.
}
move Ho: (nth_error M p) => o.
case: o Ho; first last.
{
move=> Hp + /ltac:(exfalso).
apply.
move=> /=.
by rewrite Hp.
}
move=> [j n] Hp ?.
case Hr: (S v mod (n + 1)); last by lia.
have := mod_frac_lt Hr.
have : p < length M.
{
apply /nth_error_Some.
by rewrite Hp.
}
by nia.

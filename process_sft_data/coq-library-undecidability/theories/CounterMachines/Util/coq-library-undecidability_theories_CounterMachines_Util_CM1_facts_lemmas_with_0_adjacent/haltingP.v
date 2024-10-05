Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM1.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition config_weight (M: Cm1) : Config -> nat := fun '{| state := p; value := v |} => p + length M * v.

Lemma haltingP {M : Cm1} {x: Config}: halting M x <-> (length M <= state x \/ value x = 0).
Proof.
move: x => [p c] /=.
constructor; first last.
{
case; rewrite /halting /=; last by move=> ->.
move: c => [|c]; first done.
by move=> /nth_error_None ->.
}
have [* | /nth_error_Some] : length M <= p \/ p < length M by lia.
{
by left.
}
rewrite /halting /=.
move: c => [|c]; first by (move=> *; right).
case: (nth_error M p); last done.
move=> [q n] _.
move Hr: (S c mod (n + 1)) => r.
move: r Hr => [? [_ ?] | r _ [?]]; last by lia.
exfalso.
apply: mod_frac_neq; by eassumption.

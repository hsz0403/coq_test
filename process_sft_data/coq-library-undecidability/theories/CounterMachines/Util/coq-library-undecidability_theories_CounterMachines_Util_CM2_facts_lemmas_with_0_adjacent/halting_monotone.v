Require Import List Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM2.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma halting_monotone {cm x} (n m: nat) : n <= m -> halting cm (Nat.iter n (step cm) x) -> halting cm (Nat.iter m (step cm) x).
Proof.
move=> ? ?.
have -> : m = n + (m-n) by lia.
rewrite iter_plus.
elim: (m-n); [done | by move=> * /=; congruence].

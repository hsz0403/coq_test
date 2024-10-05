Require Import List Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM2.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma halting_eq {cm c n} : halting cm c -> Nat.iter n (step cm) c = c.
Proof.
move=> Hc.
elim: n; first done.
move=> ? /= ->.
by rewrite Hc.

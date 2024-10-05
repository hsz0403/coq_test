From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From Undecidability.Shared Require Import ListAutomation.
Require Import List.
Import ListNotations ListAutomationNotations.

Lemma projection' X Y (p : X * Y -> Prop) : enumerable p -> enumerable (fun y => exists x, p (x,y)).
Proof.
intros [f].
exists (fun n => match f n with Some (x, y) => Some y | None => None end).
intros y; split.
-
intros [x ?].
eapply H in H0 as [n].
exists n.
now rewrite H0.
-
intros [n ?].
destruct (f n) as [ [] | ] eqn:E; inversion H0; subst.
exists x.
eapply H.
eauto.

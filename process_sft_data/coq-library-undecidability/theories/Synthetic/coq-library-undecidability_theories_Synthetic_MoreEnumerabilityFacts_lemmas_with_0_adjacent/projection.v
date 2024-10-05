From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From Undecidability.Shared Require Import ListAutomation.
Require Import List.
Import ListNotations ListAutomationNotations.

Lemma projection X Y (p : X * Y -> Prop) : enumerable p -> enumerable (fun x => exists y, p (x,y)).
Proof.
intros [f].
exists (fun n => match f n with Some (x, y) => Some x | None => None end).
intros; split.
-
intros [y ?].
eapply H in H0 as [n].
exists n.
now rewrite H0.
-
intros [n ?].
destruct (f n) as [ [] | ] eqn:E; inversion H0; subst.
exists y.
eapply H.
eauto.

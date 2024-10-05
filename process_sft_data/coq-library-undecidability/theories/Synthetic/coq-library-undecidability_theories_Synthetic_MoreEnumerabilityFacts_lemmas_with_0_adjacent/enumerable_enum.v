From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From Undecidability.Shared Require Import ListAutomation.
Require Import List.
Import ListNotations ListAutomationNotations.

Lemma enumerable_enum {X} {p : X -> Prop} : enumerable p <-> list_enumerable p.
Proof.
split.
eapply enumerable_list_enumerable.
eapply list_enumerable_enumerable.

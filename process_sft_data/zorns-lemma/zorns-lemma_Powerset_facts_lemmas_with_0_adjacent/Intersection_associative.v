From Coq.Sets Require Export Powerset_facts.
Require Export EnsemblesImplicit EnsemblesTactics.

Lemma Intersection_associative {X : Type} (U V W: Ensemble X) : Intersection (Intersection U V) W = Intersection U (Intersection V W).
Proof.
now extensionality_ensembles.

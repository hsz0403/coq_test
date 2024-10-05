From Coq.Sets Require Export Powerset_facts.
Require Export EnsemblesImplicit EnsemblesTactics.

Lemma Intersection_Full_set {X : Type} {U : Ensemble X} : Intersection Full_set U = U.
Proof.
now extensionality_ensembles.

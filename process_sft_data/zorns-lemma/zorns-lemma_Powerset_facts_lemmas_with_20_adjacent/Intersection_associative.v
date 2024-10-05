From Coq.Sets Require Export Powerset_facts.
Require Export EnsemblesImplicit EnsemblesTactics.

Lemma Intersection_Full_set {X : Type} {U : Ensemble X} : Intersection Full_set U = U.
Proof.
Admitted.

Lemma Intersection_associative {X : Type} (U V W: Ensemble X) : Intersection (Intersection U V) W = Intersection U (Intersection V W).
Proof.
now extensionality_ensembles.

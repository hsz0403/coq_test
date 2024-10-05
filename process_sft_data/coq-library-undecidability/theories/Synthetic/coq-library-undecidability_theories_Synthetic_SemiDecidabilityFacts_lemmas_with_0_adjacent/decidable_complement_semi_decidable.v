Require Import Undecidability.Synthetic.DecidabilityFacts.

Lemma decidable_complement_semi_decidable {X} {p : X -> Prop} : decidable p -> semi_decidable (complement p).
Proof.
intros H.
now eapply decidable_semi_decidable, dec_compl.

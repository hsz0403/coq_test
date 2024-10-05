Require Import Undecidability.Synthetic.DecidabilityFacts.

Lemma decidable_complement_semi_decidable {X} {p : X -> Prop} : decidable p -> semi_decidable (complement p).
Proof.
intros H.
Admitted.

Lemma decidable_semi_decidable {X} {p : X -> Prop} : decidable p -> semi_decidable p.
Proof.
intros [f H].
exists (fun x n => f x).
intros x.
unfold decider, reflects in H.
rewrite H.
firstorder.
econstructor.

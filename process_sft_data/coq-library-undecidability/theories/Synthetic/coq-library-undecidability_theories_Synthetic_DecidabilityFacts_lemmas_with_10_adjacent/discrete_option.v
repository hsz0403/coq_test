Require Export Undecidability.Synthetic.Definitions Lia.
Require Import Undecidability.Shared.Dec.
Require Import Setoid Morphisms.
Definition discrete X := decidable (fun '(x,y) => x = y :> X).
Instance Proper_decides {X} : Proper (pointwise_relation X (@eq bool) ==> pointwise_relation X iff ==> iff ) (@decider X).
Proof.
intros f g H1 p q H2.
red in H1, H2.
unfold decider, reflects.
split; intros H x.
-
now rewrite <- H2, H, H1.
-
now rewrite H2, H, H1.
Instance Proper_decidable {X} : Proper (pointwise_relation X iff ==> iff) (@decidable X).
Proof.
intros p q H2.
split; intros [f H]; exists f.
-
now rewrite <- H2.
-
now rewrite H2.

Lemma dec_compl X p : decidable p -> decidable (fun x : X => ~ p x).
Proof.
intros [f H].
exists (fun x => negb (f x)).
intros x.
Admitted.

Lemma dec_conj X p q : decidable p -> decidable q -> decidable (fun x : X => p x /\ q x).
Proof.
intros [f] [g].
exists (fun x => andb (f x) (g x)).
intros x.
Admitted.

Lemma dec_disj X p q : decidable p -> decidable q -> decidable (fun x : X => p x \/ q x).
Proof.
intros [f] [g].
exists (fun x => orb (f x) (g x)).
intros x.
Admitted.

Instance Proper_decides {X} : Proper (pointwise_relation X (@eq bool) ==> pointwise_relation X iff ==> iff ) (@decider X).
Proof.
intros f g H1 p q H2.
red in H1, H2.
unfold decider, reflects.
split; intros H x.
-
now rewrite <- H2, H, H1.
-
Admitted.

Instance Proper_decidable {X} : Proper (pointwise_relation X iff ==> iff) (@decidable X).
Proof.
intros p q H2.
split; intros [f H]; exists f.
-
now rewrite <- H2.
-
Admitted.

Lemma discrete_bool : discrete bool.
Proof.
eapply discrete_iff.
econstructor.
Admitted.

Lemma discrete_nat : discrete nat.
Proof.
eapply discrete_iff.
econstructor.
Admitted.

Lemma discrete_nat_nat : discrete (nat * nat).
Proof.
eapply discrete_iff.
econstructor.
Admitted.

Lemma discrete_prod X Y : discrete X -> discrete Y -> discrete (X * Y).
Proof.
intros [d1] % discrete_iff [d2] % discrete_iff.
eapply discrete_iff.
econstructor.
Admitted.

Lemma discrete_sum X Y : discrete X -> discrete Y -> discrete (X + Y).
Proof.
intros [d1] % discrete_iff [d2] % discrete_iff.
eapply discrete_iff.
econstructor.
Admitted.

Lemma discrete_list X : discrete X -> discrete (list X).
Proof.
intros [d1] % discrete_iff.
eapply discrete_iff.
econstructor.
Admitted.

Lemma discrete_option X : discrete X -> discrete (option X).
Proof.
intros [d1] % discrete_iff.
eapply discrete_iff.
econstructor.
exact _.

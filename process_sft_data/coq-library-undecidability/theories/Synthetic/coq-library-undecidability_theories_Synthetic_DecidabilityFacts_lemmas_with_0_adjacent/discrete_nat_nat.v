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

Lemma discrete_nat_nat : discrete (nat * nat).
Proof.
eapply discrete_iff.
econstructor.
exact _.

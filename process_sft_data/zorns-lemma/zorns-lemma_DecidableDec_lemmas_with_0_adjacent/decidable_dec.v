Require Import Description.
Require Import Classical.

Lemma decidable_dec: forall P:Prop, P \/ ~P -> {P} + {~P}.
Proof.
intros.
apply exclusive_dec.
tauto.
assumption.

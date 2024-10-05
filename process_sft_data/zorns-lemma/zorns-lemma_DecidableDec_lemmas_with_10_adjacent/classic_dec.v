Require Import Description.
Require Import Classical.

Lemma exclusive_dec: forall P Q:Prop, ~(P /\ Q) -> (P \/ Q) -> {P} + {Q}.
Proof.
intros.
assert ({x:bool | if x then P else Q}).
apply constructive_definite_description.
case H0.
exists true.
red; split.
assumption.
destruct x'.
reflexivity.
tauto.
exists false.
red; split.
assumption.
destruct x'.
tauto.
reflexivity.
destruct H1.
destruct x.
left.
assumption.
right.
Admitted.

Lemma decidable_dec: forall P:Prop, P \/ ~P -> {P} + {~P}.
Proof.
intros.
apply exclusive_dec.
tauto.
Admitted.

Lemma classic_dec: forall P:Prop, {P} + {~P}.
Proof.
intro P.
apply decidable_dec.
apply classic.

Require Import Description.
Require Import Classical.

Lemma classic_dec: forall P:Prop, {P} + {~P}.
Proof.
intro P.
apply decidable_dec.
apply classic.

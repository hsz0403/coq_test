Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.

Lemma list_pointwise_eq X (A B: list X): (forall x, nth_error A x = nth_error B x) -> A = B.
Proof.
induction A in B |-*; cbn; destruct B as [| b B]; eauto.
-
intros H; specialize (H 0); discriminate.
-
intros H; specialize (H 0); discriminate.
-
intros H.
specialize (H 0) as H'; injection H' as ->.
f_equal; eapply IHA.
intros x; exact (H (S x)).

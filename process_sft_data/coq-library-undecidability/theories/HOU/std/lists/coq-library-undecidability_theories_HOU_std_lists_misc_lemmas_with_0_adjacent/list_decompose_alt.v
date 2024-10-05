Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.

Lemma list_decompose_alt k {X} (A: list X): k <= length A -> exists A1 A2, A = A1 ++ A2 /\ length A2 = k.
Proof.
intros H.
assert (length A - k <= length A) by lia.
destruct (list_decompose _ H0) as (A1 & A2 & ?).
intuition.
exists A1.
exists A2.
intuition.
specialize (app_length A1 A2) as H4.
rewrite <-H2 in H4.
rewrite H4 in H3.
lia.

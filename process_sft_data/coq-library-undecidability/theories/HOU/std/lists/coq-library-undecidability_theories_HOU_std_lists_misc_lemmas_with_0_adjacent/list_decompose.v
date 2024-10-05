Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.

Lemma list_decompose k {X} (A: list X): k <= length A -> exists A1 A2, A = A1 ++ A2 /\ length A1 = k.
Proof.
induction A in k |-*; intros.
-
exists nil.
exists nil; cbn.
destruct k; intuition.
-
destruct k.
+
exists nil; exists (a :: A); intuition.
+
cbn in *; assert (k <= length A) by lia.
destruct (IHA _ H0) as (A1 & A2 & ?).
intuition.
exists (a :: A1).
exists A2.
subst.
intuition.

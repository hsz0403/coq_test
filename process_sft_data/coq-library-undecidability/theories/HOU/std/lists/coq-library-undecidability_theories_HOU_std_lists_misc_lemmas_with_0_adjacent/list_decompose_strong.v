Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.

Lemma list_decompose_strong Y k (A: list Y): k <= length A -> { A1 & { A2 | A = A1 ++ A2 /\ length A1 = k}}.
Proof.
induction A in k |-*; intros H.
-
exists nil.
exists nil.
intuition.
-
destruct k.
+
exists nil.
exists (a :: A).
intuition.
+
cbn in H; eapply le_S_n in H.
destruct (IHA _ H) as (A1 & A2 & H1 & H2); subst.
exists (a :: A1).
exists A2.
intuition.

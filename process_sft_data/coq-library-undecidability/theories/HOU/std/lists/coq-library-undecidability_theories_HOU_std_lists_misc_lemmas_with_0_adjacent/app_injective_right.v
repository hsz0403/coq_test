Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.

Lemma app_injective_right Y (A1 A2 B1 B2 : list Y): length A2 = length B2 -> A1 ++ A2 = B1 ++ B2 -> A1 = B1 /\ A2 = B2.
Proof.
intros H; induction A1 in B1 |-*; destruct B1; cbn; eauto.
1 - 2: intros; subst; cbn in H; autorewrite with list in H; lia.
intros [= -> ? % IHA1]; intuition; now subst.

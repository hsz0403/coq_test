Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.

Lemma app_injective {X} (A B C D: list X): length A = length C -> A ++ B = C ++ D -> A = C /\ B = D.
Proof.
induction A in C |-*; destruct C; try discriminate.
cbn; intuition.
injection 1 as ?.
injection 1 as ?.
subst.
edestruct IHA; eauto; subst; intuition.

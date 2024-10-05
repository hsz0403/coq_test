From Undecidability.Shared.Libs.PSL Require Import FinTypes.
Definition Cardinality (F: finType) := | elem F |.

Lemma dupfree_concat (X: Type) (A: list (list X)) : (forall B, B el A -> dupfree B) /\ (forall B C, B <> C -> B el A -> C el A -> disjoint B C) -> dupfree A -> dupfree (concat A).
Proof.
induction A.
-
constructor.
-
intros [H H'] D.
cbn.
apply dupfree_app.
+
apply disjoint_concat.
intros C E.
apply H'; auto.
inv D.
intro G; apply H2.
now subst a.
+
now apply H.
+
inv D; apply IHA; auto.

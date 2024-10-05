From Undecidability.Shared.Libs.PSL Require Import FinTypes.
Definition Cardinality (F: finType) := | elem F |.
Lemma dupfree_countOne (X: eqType) (A: list X) : (forall x, count A x <= 1) -> dupfree A.
Proof.
induction A.
-
constructor.
-
intro H.
constructor.
+
cbn in H.
specialize (H a).
deq a.
assert (count A a = 0) by lia.
now apply countZero.
+
apply IHA.
intro x.
specialize (H x).
cbn in H.
dec; lia.
Qed.
Lemma dupfree_elements (X: finType) : dupfree (elem X).
Proof.
destruct X as [X [A AI]].
assert (forall x, count A x <= 1) as H'.
{
intro x.
specialize (AI x).
lia.
}
now apply dupfree_countOne.
Qed.
Lemma dupfree_length (X: finType) (A: list X) : dupfree A -> |A| <= Cardinality X.
Proof.
unfold Cardinality.
intros D.
rewrite <- (dupfree_card D).
rewrite <- (dupfree_card (dupfree_elements X)).
apply card_le.
apply allSub.
Qed.
Lemma disjoint_concat X (A: list (list X)) (B: list X) : (forall C, C el A -> disjoint B C) -> disjoint B (concat A).
Proof.
intros H.
induction A.
-
cbn.
auto.
-
cbn.
apply disjoint_symm.
apply disjoint_app.
split; auto using disjoint_symm.
Qed.
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
Qed.
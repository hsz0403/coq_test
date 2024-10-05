From Undecidability.Shared.Libs.PSL Require Export BaseLists Filter Lists.Cardinality.
Inductive dupfree (X : Type) : list X -> Prop := | dupfreeN : dupfree nil | dupfreeC x A : ~ x el A -> dupfree A -> dupfree (x::A).
Section Dupfree.
Variable X : Type.
Implicit Types A B : list X.
End Dupfree.
Section Undup.
Variable X : eqType.
Implicit Types A B : list X.
Fixpoint undup (A : list X) : list X := match A with | nil => nil | x::A' => if Dec (x el A') then undup A' else x :: undup A' end.
End Undup.

Lemma dupfree_concat X (A: list (list X)): dupfree A -> (forall A1 A2, A1 el A -> A2 el A -> A1 <> A2 -> disjoint A1 A2) -> (forall A1, A1 el A -> dupfree A1) -> dupfree (concat A).
Proof.
induction A as [|A0 A].
-
constructor.
-
intros H1 H2 H3.
inv H1.
cbn.
eapply dupfree_app.
+
hnf.
setoid_rewrite in_concat_iff.
intros (a0&?&A1&?&?).
eapply (H2 A0 A1);eauto.
congruence.
+
eauto.
+
apply IHA.
all:eauto.

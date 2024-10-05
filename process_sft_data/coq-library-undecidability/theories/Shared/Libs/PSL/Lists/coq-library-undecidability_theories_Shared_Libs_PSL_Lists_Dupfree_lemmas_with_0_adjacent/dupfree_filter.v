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

Lemma dupfree_filter p A : dupfree A -> dupfree (filter p A).
Proof.
intros D.
induction D as [|x A C D]; cbn.
-
left.
-
destruct (p x) eqn:E; [|exact IHD].
right; [|exact IHD].
rewrite in_filter_iff, E.
intuition.

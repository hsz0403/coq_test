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

Lemma dupfree_app A B : disjoint A B -> dupfree A -> dupfree B -> dupfree (A++B).
Proof.
intros D E F.
induction E as [|x A E' E]; cbn.
-
exact F.
-
apply disjoint_cons in D as [D D'].
constructor; [|exact (IHE D')].
intros G.
apply in_app_iff in G; tauto.

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

Lemma dupfree_dec A : dec (dupfree A).
Proof.
induction A as [|x A].
-
left.
left.
-
decide (x el A) as [E|E].
+
right.
intros F.
inv F; tauto.
+
destruct (IHA) as [F|F].
*
unfold dec.
auto using dupfree.
*
right.
intros G.
inv G; tauto.

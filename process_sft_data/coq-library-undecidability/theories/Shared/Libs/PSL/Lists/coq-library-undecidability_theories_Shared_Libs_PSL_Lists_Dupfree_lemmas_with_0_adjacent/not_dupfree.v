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

Lemma not_dupfree (A:list X): ~dupfree A -> exists a A1 A2 A3, A = A1++a::A2++a::A3.
Proof.
intros DF.
induction A.
now destruct DF;eauto using dupfree.
destruct (dupfree_dec A).
decide (a el A).
-
edestruct in_split as (A2&A3&eqA).
eassumption.
rewrite eqA.
exists a,[],A2,A3.
reflexivity.
-
edestruct DF.
eauto using dupfree.
-
edestruct IHA as (a'&A1&A2&A3&->).
eassumption.
exists a',(a::A1),A2,A3.
reflexivity.

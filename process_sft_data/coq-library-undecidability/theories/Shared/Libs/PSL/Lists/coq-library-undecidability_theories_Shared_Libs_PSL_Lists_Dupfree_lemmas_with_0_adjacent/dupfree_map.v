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

Lemma dupfree_map Y A (f : X -> Y) : (forall x y, x el A -> y el A -> f x = f y -> x=y) -> dupfree A -> dupfree (map f A).
Proof.
intros D E.
induction E as [|x A E' E]; cbn.
-
constructor.
-
constructor; [|now auto].
intros F.
apply in_map_iff in F as [y [F F']].
rewrite (D y x) in F'; auto.

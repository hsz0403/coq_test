Require Export Families.
Require Export Image.
Require Import ImageImplicit.
Require Import FiniteTypes.
Require Export EnsemblesTactics.
Set Implicit Arguments.
Section IndexedFamilies.
Variable A T:Type.
Definition IndexedFamily := A -> Ensemble T.
Variable F:IndexedFamily.
Inductive IndexedUnion : Ensemble T := | indexed_union_intro: forall (a:A) (x:T), In (F a) x -> In IndexedUnion x.
Inductive IndexedIntersection : Ensemble T := | indexed_intersection_intro: forall (x:T), (forall a:A, In (F a) x) -> In IndexedIntersection x.
End IndexedFamilies.
Section IndexedFamilyFacts.
End IndexedFamilyFacts.
Section IndexedFamilyToFamily.
Variable T:Type.
Variable A:Type.
Variable F:IndexedFamily A T.
Definition ImageFamily : Family T := Im Full_set F.
End IndexedFamilyToFamily.

Lemma indexed_to_family_union: IndexedUnion F = FamilyUnion ImageFamily.
Proof.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
intuition.
destruct H.
apply family_union_intro with (F a).
apply Im_intro with a.
constructor.
reflexivity.
assumption.
destruct H.
destruct H.
apply indexed_union_intro with x0.
rewrite <- H1.
assumption.

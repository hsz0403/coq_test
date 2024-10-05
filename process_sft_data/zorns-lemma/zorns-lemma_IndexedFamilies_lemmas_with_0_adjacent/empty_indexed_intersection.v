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

Lemma empty_indexed_intersection: forall {T:Type} (F:IndexedFamily False T), IndexedIntersection F = Full_set.
Proof.
intros.
apply Extensionality_Ensembles; red; split; red; intros; auto with sets.
constructor.
constructor.
destruct a.

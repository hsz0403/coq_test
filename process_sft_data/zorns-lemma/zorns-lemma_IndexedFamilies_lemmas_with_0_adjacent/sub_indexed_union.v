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

Lemma sub_indexed_union: forall {A B T:Type} (f:A->B) (F:IndexedFamily B T), let subF := (fun a:A => F (f a)) in Included (IndexedUnion subF) (IndexedUnion F).
Proof.
unfold Included.
intros.
destruct H.
apply indexed_union_intro with (f a).
assumption.

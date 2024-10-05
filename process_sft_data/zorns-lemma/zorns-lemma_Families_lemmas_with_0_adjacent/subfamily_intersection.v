Require Export Ensembles.
Require Import EnsemblesImplicit.
Set Implicit Arguments.
Section Families.
Variable T:Type.
Definition Family := Ensemble (Ensemble T).
Variable F:Family.
Inductive FamilyUnion: Ensemble T := | family_union_intro: forall (S:Ensemble T) (x:T), In F S -> In S x -> In FamilyUnion x.
Inductive FamilyIntersection: Ensemble T := | family_intersection_intro: forall x:T, (forall S:Ensemble T, In F S -> In S x) -> In FamilyIntersection x.
End Families.
Section FamilyFacts.
Variable T:Type.
End FamilyFacts.

Lemma subfamily_intersection: forall F G:Family T, Included F G -> Included (FamilyIntersection G) (FamilyIntersection F).
Proof.
unfold Included.
intros.
constructor.
destruct H0.
intros.
apply H0.
apply H.
assumption.

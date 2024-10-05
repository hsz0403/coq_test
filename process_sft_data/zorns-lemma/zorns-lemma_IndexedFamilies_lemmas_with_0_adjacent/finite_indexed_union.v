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

Lemma finite_indexed_union {A T : Type} {F : IndexedFamily A T} : FiniteT A -> (forall a, Finite _ (F a)) -> Finite _ (IndexedUnion F).
Proof.
intro H.
induction H; intros.
-
replace (IndexedUnion F) with (@Empty_set T).
+
constructor.
+
extensionality_ensembles.
destruct a.
-
replace (IndexedUnion F) with (Union (IndexedUnion (fun t => In (F (Some t)))) (F None)).
apply Union_preserves_Finite.
+
apply IHFiniteT.
intro.
apply H0.
+
apply H0.
+
extensionality_ensembles.
*
econstructor.
eassumption.
*
econstructor.
eassumption.
*
destruct a.
**
left.
econstructor.
eassumption.
**
now right.
-
replace (IndexedUnion F) with (IndexedUnion (fun x => F (f x))).
+
apply IHFiniteT.
intro.
apply H1.
+
extensionality_ensembles.
*
econstructor.
eassumption.
*
destruct H0.
rewrite <- (H3 a) in H2.
econstructor.
eassumption.

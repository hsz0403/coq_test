Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.ClassicalFacts.
Inductive remove_rel {A: Type}: A -> list A -> list A -> Prop := | remove_rel_nil: forall a, remove_rel a nil nil | remove_rel_cons_eq: forall a xs ys, remove_rel a xs ys -> remove_rel a (a :: xs) ys | remove_rel_cons_neq: forall a b xs ys, a <> b -> remove_rel a xs ys -> remove_rel a (b :: xs) (b :: ys).
Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

Lemma prop_ext: prop_extensionality.
Proof.
hnf; intros.
set (A0 := fun x: unit => A).
set (B0 := fun x: unit => B).
assert (A0 = B0).
+
apply Extensionality_Ensembles.
split; subst A0 B0; unfold Included, Ensembles.In; intros; tauto.
+
change A with (A0 tt).
change B with (B0 tt).
rewrite H0; auto.

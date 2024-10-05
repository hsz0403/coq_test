Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_intersection: forall {X Y:Type} (f:X->Y) (T1 T2:Ensemble Y), inverse_image f (Intersection T1 T2) = Intersection (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
inversion H.
constructor; constructor; trivial.
destruct H as [? [] []].
constructor; constructor; trivial.

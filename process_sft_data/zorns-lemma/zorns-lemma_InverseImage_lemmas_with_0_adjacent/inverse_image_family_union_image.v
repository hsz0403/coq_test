Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_family_union_image {X Y : Type} (f : X -> Y) (F : Family Y) : inverse_image f (FamilyUnion F) = FamilyUnion (Im F (inverse_image f)).
Proof.
apply Extensionality_Ensembles.
split; red; intros; inversion H; inversion H0; subst; repeat econstructor; eassumption + now destruct H1.

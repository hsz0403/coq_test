Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_surjective_injective {X Y : Type} (f : X -> Y) : surjective f -> injective (inverse_image f).
Proof.
intros H U V eq.
apply Extensionality_Ensembles.
split; red; intros; destruct (H x); subst; apply (in_inverse_image f); [ rewrite <- eq | rewrite eq ]; now constructor.

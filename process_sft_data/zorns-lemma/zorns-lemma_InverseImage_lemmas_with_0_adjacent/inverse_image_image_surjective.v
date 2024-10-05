Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_image_surjective {X Y : Type} (f : X -> Y) (T : Ensemble Y) : surjective f -> Im (inverse_image f T) f = T.
Proof.
intro.
apply Extensionality_Ensembles.
split; red; intros.
-
inversion H0.
subst.
now destruct H1.
-
destruct (H x).
subst.
now repeat econstructor.

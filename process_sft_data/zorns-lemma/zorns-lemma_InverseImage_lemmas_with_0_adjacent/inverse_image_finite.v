Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_finite {X Y : Type} (f : X -> Y) (F : Family X) : surjective f -> Finite _ F -> Finite _ (inverse_image (inverse_image f) F).
Proof.
intros Hf H.
induction H.
-
rewrite inverse_image_empty_set.
constructor.
-
unfold Add.
rewrite inverse_image_union2.
pose proof (Singleton_is_finite _ (Im x f)).
now eapply Union_preserves_Finite, Finite_downward_closed, inverse_image_surjective_singleton.

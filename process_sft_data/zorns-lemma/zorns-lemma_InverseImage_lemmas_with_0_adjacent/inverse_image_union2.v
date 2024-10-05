Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_union2 {X Y : Type} (f : X -> Y) (U V : Ensemble Y) : inverse_image f (Union U V) = Union (inverse_image f U) (inverse_image f V).
Proof.
apply Extensionality_Ensembles.
split; red; intros.
-
destruct H.
inversion H; subst; [ left | right ]; now constructor.
-
now inversion H; destruct H0; subst; constructor; [ left | right ].

Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_composition: forall {X Y Z:Type} (f:Y->Z) (g:X->Y) (U:Ensemble Z), inverse_image (fun x:X => f (g x)) U = inverse_image g (inverse_image f U).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
constructor; constructor.
destruct H.
assumption.
destruct H; inversion H.
constructor; trivial.

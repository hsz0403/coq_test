Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_indexed_union : forall {A X Y:Type} (f:X->Y) (F:IndexedFamily A Y), inverse_image f (IndexedUnion F) = IndexedUnion (fun a:A => inverse_image f (F a)).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
-
destruct H.
inversion_clear H.
exists a.
constructor.
exact H0.
-
destruct H.
inversion_clear H.
constructor.
exists a.
exact H0.

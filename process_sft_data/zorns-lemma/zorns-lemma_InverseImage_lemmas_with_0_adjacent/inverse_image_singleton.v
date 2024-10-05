Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_singleton {X Y : Type} (f : X -> Y) (g : Y -> X) (T : Ensemble Y) : (forall x, g (f x) = x) -> (forall y, f (g y) = y) -> inverse_image (inverse_image g) (Singleton T) = Singleton (inverse_image f T).
Proof.
intros Hgf Hfg.
rewrite inverse_image_fun.
apply Extensionality_Ensembles.
split; red; intros; inversion H; subst; red; rewrite inverse_image_id; constructor + assumption.

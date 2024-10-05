Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_add {X Y : Type} (f : X -> Y) (g : Y -> X) (F : Family Y) (T : Ensemble Y) : (forall x, g (f x) = x) -> (forall y, f (g y) = y) -> inverse_image (inverse_image g) (Add F T) = Add (inverse_image (inverse_image g) F) (inverse_image f T).
Proof.
intros Hgf Hfg.
apply Extensionality_Ensembles.
rewrite inverse_image_fun, inverse_image_fun.
split; red; intros; inversion H; subst; (left; assumption) + (right; inversion H0; rewrite inverse_image_id; constructor + assumption).

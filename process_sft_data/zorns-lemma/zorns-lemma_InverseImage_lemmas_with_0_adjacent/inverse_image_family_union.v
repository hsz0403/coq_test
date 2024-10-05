Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_family_union {X Y : Type} {f : X -> Y} {g : Y -> X} (F : Family Y) : (forall x, g (f x) = x) -> (forall y, f (g y) = y) -> inverse_image f (FamilyUnion F) = FamilyUnion (inverse_image (inverse_image g) F).
Proof.
intros Hgf Hfg.
apply Extensionality_Ensembles.
split; red; intros.
-
apply in_inverse_image in H.
inversion H.
subst.
rewrite <- Hgf.
econstructor.
+
constructor.
erewrite inverse_image_id.
*
exact H0.
*
exact Hfg.
+
rewrite Hgf.
constructor.
assumption.
-
destruct H.
apply in_inverse_image in H.
constructor.
econstructor.
+
exact H.
+
constructor.
rewrite Hgf.
assumption.

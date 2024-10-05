Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_fun {X Y : Type} (f : X -> Y) (T : Ensemble Y) : inverse_image f T = fun x => T (f x).
Proof.
apply Extensionality_Ensembles.
Admitted.

Lemma in_inverse_image {X Y : Type} (f : X -> Y) (T : Ensemble Y) (x : X) : In T (f x) <-> In (inverse_image f T) x.
Proof.
rewrite inverse_image_fun.
Admitted.

Lemma inverse_image_id {X Y : Type} {f : X -> Y} {g : Y -> X} : (forall y, f (g y) = y) -> forall S, inverse_image g (inverse_image f S) = S.
Proof.
intros Hfg S.
rewrite <- inverse_image_composition.
apply Extensionality_Ensembles.
split; red; intros.
-
destruct H.
rewrite <- Hfg.
assumption.
-
constructor.
rewrite Hfg.
Admitted.

Lemma inverse_image_empty_set {X Y : Type} (f : X -> Y) : inverse_image f Empty_set = Empty_set.
Proof.
apply Extensionality_Ensembles.
Admitted.

Lemma inverse_image_full_set {X Y : Type} (f : X -> Y) : inverse_image f Full_set = Full_set.
Proof.
apply Extensionality_Ensembles.
Admitted.

Lemma inverse_image_union2 {X Y : Type} (f : X -> Y) (U V : Ensemble Y) : inverse_image f (Union U V) = Union (inverse_image f U) (inverse_image f V).
Proof.
apply Extensionality_Ensembles.
split; red; intros.
-
destruct H.
inversion H; subst; [ left | right ]; now constructor.
-
Admitted.

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
Admitted.

Lemma inverse_image_family_union_image {X Y : Type} (f : X -> Y) (F : Family Y) : inverse_image f (FamilyUnion F) = FamilyUnion (Im F (inverse_image f)).
Proof.
apply Extensionality_Ensembles.
Admitted.

Lemma inverse_image_singleton {X Y : Type} (f : X -> Y) (g : Y -> X) (T : Ensemble Y) : (forall x, g (f x) = x) -> (forall y, f (g y) = y) -> inverse_image (inverse_image g) (Singleton T) = Singleton (inverse_image f T).
Proof.
intros Hgf Hfg.
rewrite inverse_image_fun.
apply Extensionality_Ensembles.
Admitted.

Lemma inverse_image_add {X Y : Type} (f : X -> Y) (g : Y -> X) (F : Family Y) (T : Ensemble Y) : (forall x, g (f x) = x) -> (forall y, f (g y) = y) -> inverse_image (inverse_image g) (Add F T) = Add (inverse_image (inverse_image g) F) (inverse_image f T).
Proof.
intros Hgf Hfg.
apply Extensionality_Ensembles.
rewrite inverse_image_fun, inverse_image_fun.
Admitted.

Lemma inverse_image_surjective_singleton {X Y : Type} (f : X -> Y) (T : Ensemble X) : surjective f -> Included (inverse_image (inverse_image f) (Singleton T)) (Singleton (Im T f)).
Proof.
intros H U HU.
destruct HU.
inversion H0.
subst.
Admitted.

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
Admitted.

Lemma inverse_image_surjective_injective {X Y : Type} (f : X -> Y) : surjective f -> injective (inverse_image f).
Proof.
intros H U V eq.
apply Extensionality_Ensembles.
Admitted.

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

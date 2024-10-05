Require Export FunctionProperties.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export EnsemblesSpec.
Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X := [ x:X | In T (f x) ].
Hint Unfold inverse_image : sets.
Hint Resolve @inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full @inverse_image_intersection @inverse_image_union @inverse_image_complement @inverse_image_composition : sets.
Require Import IndexedFamilies.

Lemma inverse_image_increasing: forall {X Y:Type} (f:X->Y) (T1 T2:Ensemble Y), Included T1 T2 -> Included (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
red; intros.
destruct H0.
constructor.
Admitted.

Lemma inverse_image_empty: forall {X Y:Type} (f:X->Y), inverse_image f Empty_set = Empty_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H as [[]].
Admitted.

Lemma inverse_image_full: forall {X Y:Type} (f:X->Y), inverse_image f Full_set = Full_set.
Proof.
intros.
Admitted.

Lemma inverse_image_union: forall {X Y:Type} (f:X->Y) (T1 T2:Ensemble Y), inverse_image f (Union T1 T2) = Union (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
inversion H.
left; constructor; trivial.
right; constructor; trivial.
constructor.
destruct H as [? []|? []].
left; trivial.
Admitted.

Lemma inverse_image_complement: forall {X Y:Type} (f:X->Y) (T:Ensemble Y), inverse_image f (Complement T) = Complement (inverse_image f T).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
red; intro.
destruct H.
destruct H0.
contradiction H.
constructor.
intro.
contradiction H.
Admitted.

Lemma inverse_image_composition: forall {X Y Z:Type} (f:Y->Z) (g:X->Y) (U:Ensemble Z), inverse_image (fun x:X => f (g x)) U = inverse_image g (inverse_image f U).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
constructor; constructor.
destruct H.
assumption.
destruct H; inversion H.
Admitted.

Lemma inverse_image_indexed_intersection : forall {A X Y:Type} (f:X->Y) (F:IndexedFamily A Y), inverse_image f (IndexedIntersection F) = IndexedIntersection (fun a:A => inverse_image f (F a)).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
-
destruct H.
inversion_clear H.
constructor.
intros.
constructor.
apply H0.
-
destruct H.
constructor.
constructor.
intros.
destruct (H a).
Admitted.

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
Admitted.

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

Lemma inverse_image_intersection: forall {X Y:Type} (f:X->Y) (T1 T2:Ensemble Y), inverse_image f (Intersection T1 T2) = Intersection (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
inversion H.
constructor; constructor; trivial.
destruct H as [? [] []].
constructor; constructor; trivial.

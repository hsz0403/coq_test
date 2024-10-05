Require Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Logic.lib.Coqlib.
Arguments Included {U} B C.
Arguments Same_set {U} B C.
Add Parametric Relation {A} : (Ensemble A) Same_set reflexivity proved by (Same_set_refl A) symmetry proved by (Same_set_sym A) transitivity proved by (Same_set_trans A) as Same_set_rel.
Instance Included_proper (V: Type): Proper (Same_set ==> Same_set ==> iff) (@Included V).
Proof.
hnf; intros.
hnf; intros.
rewrite Same_set_spec in *.
unfold pointwise_relation, Included, Ensembles.In in *.
firstorder.
Defined.
Instance complement_proper (V: Type): Proper (Same_set ==> Same_set) (Complement V).
hnf; intros.
rewrite Same_set_spec in *.
hnf; intros.
unfold Complement, Ensembles.In.
specialize (H a).
tauto.
Defined.
Instance Union_proper (V: Type): Proper (Same_set ==> Same_set ==> Same_set) (Union V).
hnf; intros.
hnf; intros.
rewrite Same_set_spec in *.
unfold pointwise_relation in *; intros.
rewrite !Union_spec.
firstorder.
Defined.
Instance Disjoint_proper (V: Type): Proper (Same_set ==> Same_set ==> iff) (Disjoint V).
hnf; intros.
hnf; intros.
rewrite Same_set_spec in *.
unfold pointwise_relation in *.
rewrite !Disjoint_spec.
firstorder.
Defined.
Instance Intersection_proper {A}: Proper (Same_set ==> Same_set ==> Same_set) (Intersection A).
Proof.
do 2 (hnf; intros).
rewrite Same_set_spec in *.
intro a; specialize (H0 a); specialize (H a).
rewrite !Intersection_spec.
tauto.
Defined.
Definition app_same_set {A: Type} {P Q: Ensemble A} (H: Same_set P Q) (x: A): P x <-> Q x := proj1 (Same_set_spec A P Q) H x.
Coercion app_same_set : Same_set >-> Funclass.
Definition respectful_set {A B: Type} (X: Ensemble B) (f: A -> B): Ensemble A := fun x => X (f x).
Inductive image_set {A B: Type}: Ensemble A -> (A -> B) -> Ensemble B := | image_set_intro: forall (X: Ensemble A) (f: A -> B) (x: A), X x -> image_set X f (f x).
Instance respectful_set_proper {A B: Type}: Proper (Same_set ==> pointwise_relation A (@eq B) ==> Same_set) respectful_set.
Proof.
intros.
do 2 (hnf; intros).
rewrite Same_set_spec in *.
unfold pointwise_relation in *.
unfold respectful_set.
firstorder.
+
rewrite <- H, <- H0; firstorder.
+
rewrite H, H0; firstorder.
Instance image_set_proper2 {A B: Type}: Proper (Same_set ==> eq ==> Same_set) (@image_set A B).
Proof.
intros.
do 2 (hnf; intros).
rewrite Same_set_spec in *.
unfold pointwise_relation in *.
intros.
rewrite !image_set_spec.
firstorder.
+
subst.
firstorder.
+
subst.
firstorder.
Definition Countable_Union (A: Type) (P: nat -> Ensemble A) : Ensemble A := fun x => exists i, P i x.
Definition Non_Empty {U: Type} (A: Ensemble U): Prop := exists x, A x.
Definition Binart_set_list (U: Type) (A B: Ensemble U): nat -> Ensemble U := fun n => match n with | 0 => A | 1 => B | _ => Empty_set _ end.
Arguments Included: clear implicits.
Arguments Same_set: clear implicits.

Lemma resp_Same_set: forall {A B: Type} (X Y: Ensemble B) (f: A -> B), Same_set X Y -> Same_set (respectful_set X f) (respectful_set Y f).
Proof.
intros.
unfold Same_set in *.
Admitted.

Lemma resp_Intersection: forall {A B: Type} (X Y: Ensemble B) (f: A -> B), Same_set (respectful_set (Intersection _ X Y) f) (Intersection _ (respectful_set X f) (respectful_set Y f)).
Proof.
intros.
rewrite Same_set_spec; intros x.
unfold respectful_set.
rewrite !Intersection_spec.
Admitted.

Lemma resp_Union: forall {A B: Type} (X Y: Ensemble B) (f: A -> B) , Same_set (respectful_set (Union _ X Y) f) (Union _ (respectful_set X f) (respectful_set Y f)).
Proof.
intros.
rewrite Same_set_spec; intros x.
unfold respectful_set.
rewrite !Union_spec.
Admitted.

Lemma resp_Complement: forall {A B: Type} (X: Ensemble B) (f: A -> B), Same_set (respectful_set (Complement _ X) f) (Complement _ (respectful_set X f)).
Proof.
intros.
rewrite Same_set_spec; intros x.
unfold respectful_set, Complement, In.
Admitted.

Lemma resp_Disjoint: forall {A B: Type} (X Y: Ensemble B) (f: A -> B), Disjoint _ X Y -> Disjoint _ (respectful_set X f) (respectful_set Y f).
Proof.
intros.
rewrite <- Included_Complement_Disjoint in *.
rewrite <- resp_Complement.
Admitted.

Lemma resp_Empty: forall {A B: Type} (f: A -> B), Same_set (respectful_set (Empty_set _) f) (Empty_set _).
Proof.
intros.
rewrite Same_set_spec.
intro x.
pose proof Noone_in_empty A.
pose proof Noone_in_empty B.
Admitted.

Lemma image_Included: forall {A B: Type} (f: A -> B) (X Y: Ensemble A), Included X Y -> Included (image_set X f) (image_set Y f).
Proof.
intros.
unfold Included, In.
intro y.
rewrite !image_set_spec.
intros [x [? ?]].
exists x; split; auto.
Admitted.

Lemma image_Same_set: forall {A B: Type} (f: A -> B) (X Y: Ensemble A), Same_set X Y -> Same_set (image_set X f) (image_set Y f).
Proof.
intros.
unfold Same_set in *.
Admitted.

Lemma image_Intersection: forall {A B: Type} (X Y: Ensemble A) (f: A -> B), Included (image_set (Intersection _ X Y) f) (Intersection _ (image_set X f) (image_set Y f)).
Proof.
intros.
unfold Included, In; intros y.
rewrite !Intersection_spec, !image_set_spec.
intros [x [? ?]].
rewrite Intersection_spec in H.
Admitted.

Lemma image_Union: forall {A B: Type} (X Y: Ensemble A) (f: A -> B), Same_set (image_set (Union _ X Y) f) (Union _ (image_set X f) (image_set Y f)).
Proof.
intros.
rewrite Same_set_spec; intros y.
rewrite !Union_spec, !image_set_spec.
pose proof (fun x => Union_spec A x X Y).
Admitted.

Lemma image_Empty: forall {A B: Type} (f: A -> B), Same_set (image_set (Empty_set _) f) (Empty_set _).
Proof.
intros.
rewrite Same_set_spec.
intro x.
rewrite image_set_spec.
pose proof Noone_in_empty A.
pose proof Noone_in_empty B.
Admitted.

Lemma image_single: forall {A B: Type} (a: A) (f: A -> B), Same_set (image_set (eq a) f) (eq (f a)).
Proof.
intros.
rewrite Same_set_spec.
intro x.
rewrite image_set_spec.
split; intros; eauto.
Admitted.

Lemma Union_is_Countable_Union: forall {U: Type} (A B: Ensemble U), Same_set (Union _ A B) (Countable_Union _ (Binart_set_list _ A B)).
Proof.
intros.
rewrite Same_set_spec.
intros x.
rewrite Union_spec; unfold Countable_Union.
split.
+
intros [? | ?].
-
exists 0; auto.
-
exists 1; auto.
+
intros [[ | [ | ]] ?].
-
left; auto.
-
right; auto.
-
Admitted.

Lemma Intersection_is_Complement_Union (classic: forall P: Prop, P \/ ~ P): forall {U: Type} (A B: Ensemble U), Same_set (Intersection _ A B) (Complement _ (Union _ (Complement _ A) (Complement _ B))).
Proof.
intros.
rewrite Same_set_spec.
intros x; unfold Complement, Ensembles.In.
rewrite Union_spec, Intersection_spec.
Admitted.

Lemma image_Disjoint_rev: forall {A B: Type} (X Y: Ensemble A) (f: A -> B), Disjoint _ (image_set X f) (image_set Y f) -> Disjoint _ X Y.
Proof.
intros.
rewrite Disjoint_spec in *.
intros x ? ?.
apply (H (f x)); constructor; auto.

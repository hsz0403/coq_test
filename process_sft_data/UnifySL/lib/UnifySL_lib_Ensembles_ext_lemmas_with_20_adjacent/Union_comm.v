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

Lemma Full_set_spec: forall A (v: A), Full_set A v <-> True.
Proof.
intros.
Admitted.

Lemma Empty_set_spec: forall A (v: A), Empty_set A v <-> False.
intros.
Admitted.

Lemma Intersection_spec: forall A (v: A) P Q, Intersection _ P Q v <-> P v /\ Q v.
Proof.
intros.
split; intros.
+
inversion H; auto.
+
Admitted.

Lemma Union_spec: forall A (v: A) P Q, Union _ P Q v <-> P v \/ Q v.
Proof.
intros.
split; intros.
+
inversion H; auto.
+
Admitted.

Lemma Disjoint_spec: forall A P Q, Disjoint A P Q <-> (forall x, P x -> Q x -> False).
Proof.
intros; split; intros.
+
inversion H.
eapply H2.
unfold In; rewrite Intersection_spec; split; eauto.
+
constructor.
intros.
unfold In; rewrite Intersection_spec.
Admitted.

Lemma Singleton_spec: forall U x y, (Singleton U x) y <-> x = y.
Proof.
intros; split; intro.
+
inversion H; auto.
+
Admitted.

Lemma Included_Full_set: forall A P, Included A P (Full_set A).
Proof.
intros.
hnf; unfold In; intros.
Admitted.

Lemma Intersection_Complement: forall A (P Q: Ensemble A), Same_set A (Intersection A (Complement A P) (Complement A Q)) (Complement A (Union A P Q)).
Proof.
intros.
unfold Same_set, Included, Complement, Ensembles.In.
split; intros.
+
rewrite Union_spec.
rewrite Intersection_spec in H.
tauto.
+
rewrite Union_spec in H.
rewrite Intersection_spec.
Admitted.

Lemma Union_iff: forall U A B x, Ensembles.In U (Union U A B) x <-> Ensembles.In U A x \/ Ensembles.In U B x.
Proof.
intros; split; intros.
+
apply Constructive_sets.Union_inv; auto.
+
Admitted.

Lemma Empty_set_iff: forall U x, Ensembles.In U (Empty_set U) x <-> False.
Proof.
Admitted.

Lemma Singleton_iff: forall U x y, Ensembles.In U (Singleton U x) y <-> x = y.
Proof.
intros; split; intro.
+
inversion H; auto.
+
Admitted.

Lemma Same_set_refl: forall A (S : Ensemble A), Same_set S S.
Proof.
Admitted.

Lemma Same_set_sym: forall A (S1 S2 : Ensemble A), Same_set S1 S2 -> Same_set S2 S1.
Proof.
Admitted.

Lemma Same_set_trans: forall A (S1 S2 S3: Ensemble A), Same_set S1 S2 -> Same_set S2 S3 -> Same_set S1 S3.
Proof.
Admitted.

Lemma Same_set_spec: forall A P Q, Same_set P Q <-> (pointwise_relation A iff) P Q.
Proof.
intros.
unfold Same_set, Included, In, pointwise_relation.
Admitted.

Lemma Complement_Empty_set: forall A, Same_set (Complement A (Empty_set _)) (Full_set _).
Proof.
intros.
rewrite Same_set_spec.
intro a.
unfold Complement, Ensembles.In.
pose proof Empty_set_iff _ a.
pose proof Full_set_spec _ a.
Admitted.

Lemma Intersection_comm: forall A P Q, Same_set (Intersection A P Q) (Intersection A Q P).
Proof.
intros.
rewrite Same_set_spec; hnf; intros.
rewrite !Intersection_spec.
Admitted.

Lemma Intersection_assoc: forall A P Q R, Same_set (Intersection A (Intersection A P Q) R) (Intersection A P (Intersection A Q R)).
Proof.
intros.
rewrite Same_set_spec; hnf; intros.
rewrite !Intersection_spec.
Admitted.

Lemma Union_assoc: forall A P Q R, Same_set (Union A (Union A P Q) R) (Union A P (Union A Q R)).
Proof.
intros.
rewrite Same_set_spec; hnf; intros.
rewrite !Union_spec.
Admitted.

Lemma Intersection_Union_distr_l: forall A P Q R, Same_set (Intersection A (Union A Q R) P) (Union A (Intersection A Q P) (Intersection A R P)).
Proof.
intros.
rewrite Same_set_spec; intro x.
rewrite !Intersection_spec, !Union_spec, !Intersection_spec.
Admitted.

Lemma Intersection_Union_distr_r: forall A P Q R, Same_set (Intersection A P (Union A Q R)) (Union A (Intersection A P Q) (Intersection A P R)).
Proof.
intros.
rewrite Same_set_spec; intro x.
rewrite !Intersection_spec, !Union_spec, !Intersection_spec.
Admitted.

Instance Included_proper (V: Type): Proper (Same_set ==> Same_set ==> iff) (@Included V).
Proof.
hnf; intros.
hnf; intros.
rewrite Same_set_spec in *.
unfold pointwise_relation, Included, Ensembles.In in *.
Admitted.

Instance complement_proper (V: Type): Proper (Same_set ==> Same_set) (Complement V).
hnf; intros.
rewrite Same_set_spec in *.
hnf; intros.
unfold Complement, Ensembles.In.
specialize (H a).
Admitted.

Instance Union_proper (V: Type): Proper (Same_set ==> Same_set ==> Same_set) (Union V).
hnf; intros.
hnf; intros.
rewrite Same_set_spec in *.
unfold pointwise_relation in *; intros.
rewrite !Union_spec.
Admitted.

Instance Disjoint_proper (V: Type): Proper (Same_set ==> Same_set ==> iff) (Disjoint V).
hnf; intros.
hnf; intros.
rewrite Same_set_spec in *.
unfold pointwise_relation in *.
rewrite !Disjoint_spec.
Admitted.

Lemma Union_Included {A: Type}: forall P Q R, Included (Union A P Q) R <-> Included P R /\ Included Q R.
Proof.
intros.
unfold Included.
pose proof Union_iff A P Q.
Admitted.

Lemma left_Included_Union {A: Type}: forall P Q, Included P (Union A P Q).
Proof.
intros.
intros ? ?.
rewrite Union_iff.
Admitted.

Lemma right_Included_Union {A: Type}: forall P Q, Included Q (Union A P Q).
Proof.
intros.
intros ? ?.
rewrite Union_iff.
Admitted.

Lemma Union_Empty_left {A: Type}: forall P, Same_set (Union _ (Empty_set A) P) P.
Proof.
intros.
rewrite Same_set_spec.
hnf; intros.
rewrite Union_spec.
pose proof Noone_in_empty A a.
Admitted.

Lemma Union_Empty_right {A: Type}: forall P, Same_set (Union _ P (Empty_set A)) P.
Proof.
intros.
rewrite Same_set_spec.
hnf; intros.
rewrite Union_spec.
pose proof Noone_in_empty A a.
Admitted.

Lemma Intersection_Full_left {A: Type}: forall P, Same_set (Intersection _ (Full_set A) P) P.
Proof.
intros.
rewrite Same_set_spec.
hnf; intros.
rewrite Intersection_spec.
pose proof Full_set_spec A a.
Admitted.

Lemma Intersection_Full_right {A: Type}: forall P, Same_set (Intersection _ P (Full_set A)) P.
Proof.
intros.
rewrite Same_set_spec.
hnf; intros.
rewrite Intersection_spec.
pose proof Full_set_spec A a.
Admitted.

Lemma Intersection_Empty_left {A: Type}: forall P, Same_set (Intersection _ (Empty_set A) P) (Empty_set A).
Proof.
intros.
rewrite Same_set_spec.
hnf; intros.
rewrite Intersection_spec.
pose proof Empty_set_spec A a.
Admitted.

Lemma Intersection_Empty_right {A: Type}: forall P, Same_set (Intersection _ P (Empty_set A)) (Empty_set A).
Proof.
intros.
rewrite Same_set_spec.
hnf; intros.
rewrite Intersection_spec.
pose proof Empty_set_spec A a.
Admitted.

Lemma Intersection_absort_right: forall U (A B: Ensemble U), Included A B -> Same_set (Intersection _ A B) A.
Proof.
intros.
rewrite Same_set_spec; intro x.
rewrite Intersection_spec.
specialize (H x); unfold Ensembles.In in H.
Admitted.

Lemma Intersection_absort_left: forall U (A B: Ensemble U), Included B A -> Same_set (Intersection _ A B) B.
Proof.
intros.
rewrite Same_set_spec; intro x.
rewrite Intersection_spec.
specialize (H x); unfold Ensembles.In in H.
Admitted.

Lemma Complement_Included_rev: forall (U: Type) P Q, Included P Q -> Included (Complement U Q) (Complement U P).
Proof.
unfold Included, Complement, Ensembles.In.
intros.
Admitted.

Instance Intersection_proper {A}: Proper (Same_set ==> Same_set ==> Same_set) (Intersection A).
Proof.
do 2 (hnf; intros).
rewrite Same_set_spec in *.
intro a; specialize (H0 a); specialize (H a).
rewrite !Intersection_spec.
Admitted.

Lemma Union_comm: forall A P Q, Same_set (Union A P Q) (Union A Q P).
Proof.
intros.
rewrite Same_set_spec; hnf; intros.
rewrite !Union_spec.
tauto.

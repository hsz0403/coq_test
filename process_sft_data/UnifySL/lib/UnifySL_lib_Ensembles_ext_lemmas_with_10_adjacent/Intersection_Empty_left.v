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

Lemma Included_Disjoint: forall A P Q P' Q', Included P P' -> Included Q Q' -> Disjoint A P' Q' -> Disjoint A P Q.
Proof.
intros.
rewrite Disjoint_spec in H1 |- *.
intros; apply (H1 x).
+
apply H; auto.
+
Admitted.

Lemma Union_left_Disjoint: forall A P Q R, Disjoint A (Union A P Q) R <-> Disjoint A P R /\ Disjoint A Q R.
Proof.
intros.
rewrite !Disjoint_spec.
pose proof (fun x => Union_spec A x P Q).
Admitted.

Lemma Union_right_Disjoint: forall A P Q R, Disjoint A R (Union A P Q) <-> Disjoint A R P /\ Disjoint A R Q.
Proof.
intros.
rewrite !Disjoint_spec.
pose proof (fun x => Union_spec A x P Q).
Admitted.

Lemma Included_Complement_Disjoint: forall A P Q, (Included P (Complement _ Q)) <-> Disjoint A P Q.
Proof.
intros.
unfold Included, Complement, In.
rewrite Disjoint_spec.
Admitted.

Lemma Disjoint_comm: forall A P Q, Disjoint A P Q <-> Disjoint A Q P.
Proof.
intros.
rewrite !Disjoint_spec.
Admitted.

Lemma Intersection_Empty_left {A: Type}: forall P, Same_set (Intersection _ (Empty_set A) P) (Empty_set A).
Proof.
intros.
rewrite Same_set_spec.
hnf; intros.
rewrite Intersection_spec.
pose proof Empty_set_spec A a.
tauto.

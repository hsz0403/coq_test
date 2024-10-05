Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Export Logic.lib.Relation_ext.
Instance list_Reflexive {A R} {EqA: @Equivalence A R}: Reflexive (Forall2 (@equiv A _ _)).
Proof.
hnf; intros.
induction x; constructor.
+
reflexivity.
+
auto.
Instance list_Symmetric {A R} {EqA: @Equivalence A R}: Symmetric (Forall2 (@equiv A _ _)).
Proof.
hnf; intros.
revert y H; induction x; intros; destruct y; try solve [inversion H]; constructor.
+
inversion H; subst.
symmetry.
auto.
+
inversion H; subst.
apply IHx; auto.
Instance list_Transitive {A R} {EqA: @Equivalence A R}: Transitive (Forall2 (@equiv A _ _)).
Proof.
hnf; intros.
revert y z H H0; induction x; intros; destruct y, z; try solve [inversion H; subst; inversion H0]; constructor.
+
inversion H; inversion H0; subst.
etransitivity; eauto.
+
inversion H; inversion H0; subst.
eapply IHx; eauto.
Instance list_Equivalence {A R} {EqA: @Equivalence A R}: Equivalence (Forall2 (@equiv A _ _)).
Proof.
split.
apply list_Reflexive.
apply list_Symmetric.
apply list_Transitive.

Lemma resp_Transitive {A B} (f: A -> B) (R: relation B) {TR: Transitive R}: Transitive (respectful_relation f R).
Proof.
intros.
hnf; intros.
unfold respectful_relation.
transitivity (f y); auto.

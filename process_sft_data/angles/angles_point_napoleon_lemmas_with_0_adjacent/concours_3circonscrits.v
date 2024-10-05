Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_cocyclicite.
Hint Resolve colineaire_sym.
Hint Resolve colineaire_modulo_pi.
Hint Resolve orthogonal_opp.
Hint Resolve double_orthogonal.
Hint Resolve critere_orthogonal critere_orthogonal_reciproque.
Definition bissectrice (I A B C : PO) := R (cons (vec A B) (vec A I)) (cons (vec A I) (vec A C)).
Hint Resolve bissectrice_double.
Hint Resolve bissectrice_unicite.
Hint Resolve bissectrice_direction.
Hint Resolve orthogonal_bissectrice.
Hint Resolve bissectrice_droite.
Definition milieu (I B C : PO) := colineaire (vec B I) (vec B C) /\ (forall A : PO, isocele A B C -> bissectrice I A B C).
Axiom existence_milieu : forall B C : PO, exists I : PO, milieu I B C.
Axiom point_aligne : forall A B C : PO, colineaire (vec A B) (vec C B) -> colineaire (vec A B) (vec A C).

Lemma concours_3circonscrits : forall A B C P Q T O1 O2 I : PO, circonscrit T A B O1 -> circonscrit I A B O1 -> circonscrit Q A C O2 -> circonscrit I A C O2 -> ~ colineaire (vec P B) (vec P C) -> R (plus (cons (vec P C) (vec P B)) (plus (cons (vec T B) (vec T A)) (cons (vec Q A) (vec Q C)))) pi -> sont_cocycliques P B C I.
unfold circonscrit in |- *; intros A B C P Q T O O' I H H0 H1 H2 H3 H4.
apply reciproque_cocyclique; auto.
apply symetrique.
apply transitive with (double (plus (cons (vec I B) (vec I A)) (cons (vec I A) (vec I C)))); auto.
apply transitive with (double (plus (cons (vec T B) (vec T A)) (cons (vec Q A) (vec Q C)))); auto.
apply regulier with (a := double (cons (vec P C) (vec P B))) (c := double (cons (vec P C) (vec P B))); auto.
apply transitive with (double (plus (cons (vec P C) (vec P B)) (cons (vec P B) (vec P C)))); auto.
apply transitive with (double (cons (vec P C) (vec P C))); auto.
apply transitive with (double zero); auto.
apply transitive with (double (plus (cons (vec P C) (vec P B)) (plus (cons (vec T B) (vec T A)) (cons (vec Q A) (vec Q C))))); auto.
apply transitive with (double pi); auto.
apply transitive with zero; auto.
apply transitive with (plus (double (cons (vec T B) (vec T A))) (double (cons (vec Q A) (vec Q C)))); auto.
apply transitive with (plus (double (cons (vec I B) (vec I A))) (double (cons (vec I A) (vec I C)))); auto.
apply compatible.
apply cocyclique with O.
elim H0; intros H5 H6; clear H0; auto.
elim H0; intros H5 H6; elim H6; intros H7 H8; clear H6 H0; auto.
elim H0; intros H5 H6; elim H6; intros H7 H8; clear H6 H0; auto.
elim H; intros H5 H6; elim H6; intros H7 H8; clear H6 H; auto.
elim H; intros H5 H6; elim H6; intros H7 H8; clear H6 H; auto.
apply cocyclique with O'.
elim H2; intros H5 H6; clear H2; try exact H5.
elim H2; intros H5 H6; elim H6; intros H7 H8; clear H6 H2; auto.
elim H2; intros H5 H6; elim H6; intros H7 H8; clear H6 H2; auto.
elim H1; intros H5 H6; elim H6; intros H7 H8; clear H6 H1; auto.
elim H1; intros H5 H6; elim H6; intros H7 H8; clear H6 H1; auto.

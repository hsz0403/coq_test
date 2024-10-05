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

Lemma isocele_bissectrice_hauteur : forall I A B C : PO, bissectrice I A B C -> isocele A B C -> orthogonal (vec A I) (vec B C).
unfold isocele, orthogonal, bissectrice in |- *; intros I A B C H H0.
apply transitive with (double (plus (cons (vec A I) (vec A C)) (plus (cons (vec A C) (vec C A)) (cons (vec C A) (vec B C))))); auto.
apply transitive with (plus (double (cons (vec A I) (vec A C))) (double (plus (cons (vec A C) (vec C A)) (cons (vec C A) (vec B C))))); auto.
apply transitive with (plus (cons (vec A B) (vec A C)) (plus (double (cons (vec A C) (vec C A))) (double (cons (vec C A) (vec B C))))); auto.
apply compatible; auto.
apply transitive with (plus (cons (vec A B) (vec A C)) (plus (double pi) (double (cons (vec C A) (vec B C))))); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (cons (vec A B) (vec A C)) (plus zero (double (cons (vec C A) (vec B C))))); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (cons (vec A B) (vec A C)) (double (cons (vec B C) (vec B A)))); auto.
apply compatible; auto.
apply transitive with (double (cons (vec C A) (vec C B))); auto.
apply transitive with (double (cons (vec C A) (vec B C))); auto.
apply transitive with (double (plus (cons (vec C A) (vec C B)) (cons (vec C B) (vec B C)))); auto.
apply transitive with (plus (double (cons (vec C A) (vec C B))) (double (cons (vec C B) (vec B C)))); auto.
apply transitive with (plus (double (cons (vec C A) (vec C B))) zero); auto.
apply compatible; auto.
apply transitive with (double pi); auto.
apply transitive with (plus zero (double (cons (vec C A) (vec C B)))); auto.
apply triangle_isocele; auto.

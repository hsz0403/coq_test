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

Lemma bissectrice_hauteur_isocele : forall I A B C : PO, bissectrice I A B C -> orthogonal (vec A I) (vec B C) -> isocele A B C.
unfold isocele, bissectrice in |- *; intros I A B C H H0.
apply reflexion with (vec A I); auto.
apply transitive with (cons (opp (vec B C)) (vec A I)); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply transitive with (plus (cons (vec C A) (vec A C)) (cons (vec A C) (vec A I))); auto.
apply transitive with (plus (cons (vec A I) (vec A B)) (cons (vec A B) (vec B A))); auto.
apply transitive with (plus (cons (vec A B) (vec B A)) (cons (vec A I) (vec A B))); auto.
apply compatible; auto.
apply transitive with pi; auto.

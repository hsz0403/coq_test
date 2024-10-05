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

Lemma isocele_hauteur_bissectrice : forall I A B C : PO, isocele A B C -> orthogonal (vec A I) (vec B C) -> bissectrice I A B C.
unfold bissectrice, isocele in |- *; intros.
generalize (critere_orthogonal_reciproque (u:=vec B C) (v:=vec A I)); intros H2; try exact H2.
apply transitive with (plus (cons (vec A B) (vec C B)) (cons (vec C B) (vec A I))); auto.
apply transitive with (plus (cons (vec B C) (vec A C)) (cons (opp (vec B C)) (vec A I))); auto.
apply compatible; auto.
apply transitive with (cons (opp (vec B A)) (opp (vec B C))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply v_sym; apply opp_vect.
apply transitive with (cons (opp (vec C B)) (opp (vec C A))); auto.
apply transitive with (cons (vec C B) (vec C A)); auto.
apply transitive with (cons (vec B A) (vec B C)); auto.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply transitive with (plus (cons (vec B C) (vec A C)) (cons (vec A I) (vec B C))); auto.
apply compatible; auto.
apply transitive with (plus (cons (vec A I) (vec B C)) (cons (vec B C) (vec A C))); auto.

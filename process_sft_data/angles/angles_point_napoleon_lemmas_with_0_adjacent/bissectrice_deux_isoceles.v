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

Lemma bissectrice_deux_isoceles : forall I A B C D : PO, bissectrice I A B C -> isocele A B C -> isocele D B C -> R (cons (vec D B) (vec A I)) (cons (vec A I) (vec D C)).
unfold isocele, bissectrice in |- *; intros I A B C D H H0 H1.
cut (R (cons (vec B C) (vec A I)) (cons (vec A I) (vec C B))); intros.
cut (R (cons (vec B D) (vec B C)) (cons (vec C B) (vec C D))); intros; auto.
apply transitive with (plus (cons (vec D B) (vec B D)) (cons (vec B D) (vec A I))); auto.
apply transitive with (plus (cons (vec A I) (vec I A)) (cons (vec I A) (vec D C))); auto.
apply compatible; auto.
apply transitive with pi; auto.
apply transitive with (plus (cons (vec B D) (vec B C)) (cons (vec B C) (vec A I))); auto.
apply transitive with (plus (cons (vec C B) (vec C D)) (cons (vec B C) (vec A I))); auto.
apply compatible; auto.
apply transitive with (plus (cons (vec C B) (vec C D)) (cons (vec A I) (vec C B))); auto.
apply compatible; auto.
apply transitive with (plus (cons (vec A I) (vec C B)) (cons (vec C B) (vec C D))); auto.
apply transitive with (cons (vec A I) (vec C D)); auto.
apply transitive with (cons (opp (vec I A)) (opp (vec D C))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply v_sym; apply opp_vect.
cut (orthogonal (vec A I) (vec B C)); intros; auto.
apply transitive with (cons (vec A I) (opp (vec B C))); auto.
apply vR_R_compatible; auto.
apply opp_vect.
apply isocele_bissectrice_hauteur; auto.

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

Lemma existence_mediatrice_base_isocele : forall A B C D : PO, isocele A B C -> isocele D B C -> bissectrice D A B C /\ bissectrice A D B C.
intros A B C D H H0; try assumption.
elim existence_milieu with (B := B) (C := C); intros I H1; try exact H1.
cut (bissectrice I A B C /\ bissectrice I D B C); intros.
elim H2; intros H3 H4; clear H2; try exact H3.
cut (colineaire (vec A I) (vec D I)); intros.
unfold bissectrice in |- *.
split; [ idtac | try assumption ].
apply bissectrice_droite with (vec A I); auto.
apply point_aligne; auto.
apply bissectrice_droite with (vec D I); auto.
apply point_aligne; auto.
apply bissectrice_direction with (1 := H3); auto.
apply bissectrice_deux_isoceles; auto.
split; [ idtac | try assumption ].
apply milieu_isocele; auto.
apply milieu_isocele; auto.

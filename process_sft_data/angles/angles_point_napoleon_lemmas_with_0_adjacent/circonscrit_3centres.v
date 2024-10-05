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

Lemma circonscrit_3centres : forall A B C O1 O2 O3 I : PO, circonscrit I A B O1 -> circonscrit I A C O2 -> circonscrit I B C O3 -> R (double (cons (vec O1 O2) (vec O1 O3))) (double (cons (vec I A) (vec I B))) /\ R (double (cons (vec O1 O3) (vec O2 O3))) (double (cons (vec I B) (vec I C))) /\ R (double (cons (vec O1 O2) (vec O2 O3))) (double (cons (vec I A) (vec I C))).
unfold circonscrit in |- *; intros A B C O1 O2 O3 I H H0 H1.
elim H1; intros H6 H7; elim H7; intros H8 H9; clear H7 H1; try exact H8.
elim H0; intros H1 H7; elim H7; intros H10 H11; clear H7 H0; try exact H10.
elim H; intros H0 H7; elim H7; intros H12 H13; clear H7 H; try exact H12.
elim existence_mediatrice_base_isocele with (A := O2) (B := I) (C := A) (D := O1); auto; intros.
elim existence_mediatrice_base_isocele with (A := O1) (B := I) (C := B) (D := O3); auto; intros.
elim existence_mediatrice_base_isocele with (A := O3) (B := I) (C := C) (D := O2); auto; intros.
split; [ apply double_orthogonal; auto | split; apply double_orthogonal; auto ].
apply isocele_bissectrice_hauteur; auto.
apply isocele_bissectrice_hauteur; auto.
apply isocele_bissectrice_hauteur; auto.
apply isocele_bissectrice_hauteur; auto.
apply isocele_bissectrice_hauteur; auto.
apply isocele_bissectrice_hauteur; auto.

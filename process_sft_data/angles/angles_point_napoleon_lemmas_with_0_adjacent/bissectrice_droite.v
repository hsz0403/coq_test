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

Lemma bissectrice_droite : forall u v w t : V, R (cons v u) (cons u w) -> colineaire u t -> R (cons v t) (cons t w).
unfold colineaire in |- *; intros u v w t H H0.
apply transitive with (plus (cons v u) (cons u t)); auto.
apply transitive with (plus (cons u w) (cons u t)); auto.
apply compatible; auto.
apply regulier with (a := cons u t) (c := cons u t); auto.
apply transitive with (cons u w); auto.
apply transitive with (plus (cons u t) (plus (cons u t) (cons u w))); auto.
apply compatible; auto.
apply transitive with (plus (plus (cons u t) (cons u t)) (cons u w)); auto.
apply transitive with (plus zero (cons u w)); auto.
apply compatible; auto.

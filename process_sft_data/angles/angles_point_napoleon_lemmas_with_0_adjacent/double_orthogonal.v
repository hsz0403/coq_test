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

Lemma double_orthogonal : forall u u' v v' : V, orthogonal u u' -> orthogonal v v' -> R (double (cons u v)) (double (cons u' v')).
unfold orthogonal in |- *; intros.
apply transitive with (double (plus (cons u u') (plus (cons u' v') (cons v' v)))); auto.
apply transitive with (plus (double (cons u u')) (double (plus (cons u' v') (cons v' v)))); auto.
apply transitive with (plus (double (cons u u')) (plus (double (cons u' v')) (double (cons v' v)))); auto.
apply compatible; auto.
apply transitive with (plus pi (plus (double (cons u' v')) pi)); auto.
apply compatible; auto.
apply compatible; auto.
apply regulier with (a := double (cons v v')) (c := pi); auto.
apply transitive with (double (plus (cons v v') (cons v' v))); auto.
apply transitive with (double (cons v v)); auto.
apply transitive with (double zero); auto.
apply transitive with zero; auto.
apply transitive with (plus (plus (double (cons u' v')) pi) pi); auto.
apply transitive with (plus (double (cons u' v')) (plus pi pi)); auto.
apply transitive with (plus (double (cons u' v')) zero); auto.
apply compatible; auto.
apply transitive with (plus zero (double (cons u' v'))); auto.

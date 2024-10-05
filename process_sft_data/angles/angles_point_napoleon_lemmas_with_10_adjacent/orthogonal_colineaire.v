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

Lemma colineaire_sym : forall u v : V, colineaire u v -> colineaire v u.
unfold colineaire in |- *; intros.
apply regulier with (a := double (cons u v)) (c := double (cons u v)); auto.
apply transitive with (double (plus (cons u v) (cons v u))); auto.
apply transitive with (double zero); auto.
apply transitive with (plus zero zero); auto.
Admitted.

Lemma colineaire_modulo_pi : forall u v u' v' : V, colineaire u u' -> colineaire v v' -> R (double (cons u' v')) (double (cons u v)).
unfold colineaire in |- *; intros.
apply transitive with (double (plus (cons u' u) (plus (cons u v) (cons v v')))); auto.
apply transitive with (plus (double (cons u' u)) (double (plus (cons u v) (cons v v')))); auto.
apply transitive with (plus (double (cons u' u)) (plus (double (cons u v)) (double (cons v v')))); auto.
apply compatible; auto.
apply transitive with (plus zero (plus (double (cons u v)) (double (cons v v')))); auto.
apply compatible; auto.
cut (colineaire u' u); intros; auto.
apply transitive with (plus (double (cons u v)) (double (cons v v'))); auto.
apply transitive with (plus (double (cons u v)) zero); auto.
apply compatible; auto.
Admitted.

Lemma orthogonal_opp : forall u v : V, orthogonal u v -> orthogonal u (opp v).
unfold orthogonal in |- *; intros.
apply transitive with (double (plus (cons u v) (cons v (opp v)))); auto.
apply transitive with (plus (double (cons u v)) (double (cons v (opp v)))); auto.
apply transitive with (plus pi (double pi)); auto.
apply compatible; auto.
apply transitive with (plus pi zero); auto.
apply compatible; auto.
Admitted.

Lemma colineaire_transitive : forall u v w : V, colineaire u v -> colineaire v w -> colineaire u w.
unfold colineaire in |- *; intros.
apply transitive with (double (plus (cons u v) (cons v w))); auto.
apply transitive with (plus (double (cons u v)) (double (cons v w))); auto.
apply transitive with (plus zero zero); auto.
Admitted.

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
Admitted.

Lemma critere_orthogonal : forall u v : V, R (cons u v) (cons v (opp u)) -> orthogonal u v.
intros u v H; unfold orthogonal, double in |- *.
apply transitive with (plus (cons u v) (cons v (opp u))); auto.
apply compatible; auto.
Admitted.

Lemma critere_orthogonal_reciproque : forall u v : V, orthogonal u v -> R (cons u v) (cons v (opp u)).
unfold orthogonal, double in |- *; intros u v H.
apply transitive with (plus (cons v u) pi); auto.
apply regulier with (a := cons u v) (c := cons u v); auto.
apply transitive with pi; auto.
apply transitive with (plus (plus (cons u v) (cons v u)) pi); auto.
apply transitive with (plus zero pi); auto.
Admitted.

Lemma bissectrice_double : forall I A B C : PO, bissectrice I A B C -> R (double (cons (vec A I) (vec A C))) (cons (vec A B) (vec A C)).
unfold bissectrice, double in |- *; intros.
apply transitive with (plus (cons (vec A B) (vec A I)) (cons (vec A I) (vec A C))); auto.
Admitted.

Lemma bissectrice_unicite : forall I A B C J : PO, bissectrice I A B C -> bissectrice J A B C -> colineaire (vec A I) (vec A J).
unfold colineaire in |- *; intros.
apply transitive with (double (plus (cons (vec A I) (vec A B)) (cons (vec A B) (vec A J)))); auto.
apply transitive with (plus (double (cons (vec A I) (vec A B))) (double (cons (vec A B) (vec A J)))); auto.
apply transitive with (plus (cons (vec A C) (vec A B)) (cons (vec A B) (vec A C))); auto.
apply compatible; unfold double in |- *.
apply transitive with (plus (cons (vec A C) (vec A I)) (cons (vec A I) (vec A B))); auto.
apply compatible; auto.
apply transitive with (plus (cons (vec A B) (vec A J)) (cons (vec A J) (vec A C))); auto.
Admitted.

Lemma bissectrice_direction : forall (I A B C : PO) (u : V), bissectrice I A B C -> R (cons (vec A B) u) (cons u (vec A C)) -> colineaire (vec A I) u.
unfold colineaire in |- *; intros.
apply transitive with (double (plus (cons (vec A I) (vec A B)) (cons (vec A B) u))); auto.
apply transitive with (plus (double (cons (vec A I) (vec A B))) (double (cons (vec A B) u))); auto.
apply transitive with (plus (cons (vec A C) (vec A B)) (cons (vec A B) (vec A C))); auto.
apply compatible; unfold double in |- *.
apply transitive with (plus (cons (vec A C) (vec A I)) (cons (vec A I) (vec A B))); auto.
apply compatible; auto.
apply transitive with (plus (cons (vec A B) u) (cons u (vec A C))); auto.
Admitted.

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
Admitted.

Lemma orthogonal_bissectrice : forall u v : V, orthogonal u v -> R (cons (opp v) u) (cons u v).
intros u v H; try assumption.
apply regulier with (a := cons u v) (c := cons u v); auto.
apply transitive with (plus (cons (opp v) u) (cons u v)); auto.
apply transitive with (cons (opp v) v); auto.
Admitted.

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
Admitted.

Lemma orthogonal_colineaire : forall u v w : V, orthogonal u v -> colineaire v w -> orthogonal u w.
unfold colineaire, orthogonal in |- *; intros.
apply transitive with (double (plus (cons u v) (cons v w))); auto.
apply transitive with (plus (double (cons u v)) (double (cons v w))); auto.
apply transitive with (plus pi zero); auto.
apply compatible; auto.
apply transitive with (plus zero pi); auto.

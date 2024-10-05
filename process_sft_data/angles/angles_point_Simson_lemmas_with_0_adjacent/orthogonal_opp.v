Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_cocyclicite.
Hint Resolve colineaire_sym.
Hint Resolve colineaire_modulo_pi.
Hint Resolve orthogonal_opp.

Lemma orthogonal_opp : forall u v : V, orthogonal u v -> orthogonal u (opp v).
unfold orthogonal in |- *; intros.
apply transitive with (double (plus (cons u v) (cons v (opp v)))); auto.
apply transitive with (plus (double (cons u v)) (double (cons v (opp v)))); auto.
apply transitive with (plus pi (double pi)); auto.
apply compatible; auto.
apply transitive with (plus pi zero); auto.
apply compatible; auto.
apply transitive with (plus zero pi); auto.

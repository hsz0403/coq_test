Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_cocyclicite.
Hint Resolve colineaire_sym.
Hint Resolve colineaire_modulo_pi.
Hint Resolve orthogonal_opp.

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
apply transitive with (plus zero (double (cons u v))); auto.

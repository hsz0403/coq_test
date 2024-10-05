Set Implicit Arguments.
Unset Strict Implicit.
Require Export point_angle.
Parameter pisurdeux : AV.
Axiom double_pisurdeux : R (double pisurdeux) pi.
Hint Resolve double_pisurdeux.
Hint Resolve abba.
Axiom construction_circonscrit : forall M A B : PO, ~ colineaire (vec M A) (vec M B) -> exists O : PO, isocele O A B /\ isocele O A M /\ isocele O B M.
Definition circonscrit (M A B O : PO) := isocele O A B /\ isocele O A M /\ isocele O B M.
Definition sont_cocycliques (M A B M' : PO) := ex (fun O : PO => ex (fun O' : PO => (circonscrit M A B O /\ circonscrit M' A B O') /\ colineaire (vec O A) (vec O' A) /\ colineaire (vec O B) (vec O' B))).
Hint Resolve isocele_sym.

Lemma unicite_perpendiculaire : forall u v u' v' : V, colineaire u u' -> orthogonal u v -> orthogonal u' v' -> colineaire v v'.
unfold colineaire in |- *.
intros u v u' v' H H0 H1; try assumption.
apply transitive with (double (plus (cons v u) (plus (cons u u') (cons u' v')))); auto.
apply transitive with (plus (double (cons v u)) (double (plus (cons u u') (cons u' v')))); auto.
apply transitive with (plus (double (cons v u)) (plus (double (cons u u')) (double (cons u' v')))); auto.
apply compatible; auto.
apply transitive with (plus pi (plus zero pi)); auto.
apply compatible; auto.
cut (orthogonal v u); (intros; auto).
apply compatible; auto.
apply transitive with (plus pi pi); auto.
apply compatible; auto.

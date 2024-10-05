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

Theorem reciproque_cocyclique : forall M A B M' : PO, ~ colineaire (vec M A) (vec M B) -> R (double (cons (vec M' A) (vec M' B))) (double (cons (vec M A) (vec M B))) -> sont_cocycliques M A B M'.
unfold sont_cocycliques in |- *.
intros M A B M' H H0; try assumption.
elim construction_circonscrit with (M := M) (A := A) (B := B); [ intros O H2; try exact H2 | auto ].
exists O.
elim construction_circonscrit with (M := M') (A := A) (B := B); [ intros O' H1; try exact H1 | auto ].
exists O'.
split; [ split; [ idtac | try assumption ] | idtac ].
try exact H2.
elim H1; intros H3 H4; elim H4; intros H5 H6; clear H4 H1; try exact H5.
elim H2; intros H1 H4; elim H4; intros H7 H8; clear H4 H2; try exact H7.
cut (R (cons (vec O A) (vec O B)) (cons (vec O' A) (vec O' B))); intros.
elim construction_orthogonal with (u := vec O A); intros u H'; try exact H'.
elim construction_orthogonal with (u := vec O' A); intros v H9; try exact H9.
elim v_vec with (u := u) (A := A); intros T H10; try exact H10.
elim v_vec with (u := v) (A := A); intros T' H11; try exact H11.
cut (colineaire (vec O A) (vec O' A)); intros.
split; [ try assumption | idtac ].
unfold colineaire in |- *.
apply transitive with (double (plus (cons (vec O B) (vec O A)) (plus (cons (vec O A) (vec O' A)) (cons (vec O' A) (vec O' B))))); auto.
apply transitive with (plus (double (cons (vec O B) (vec O A))) (double (plus (cons (vec O A) (vec O' A)) (cons (vec O' A) (vec O' B))))); auto.
apply transitive with (plus (double (cons (vec O B) (vec O A))) (plus (double (cons (vec O A) (vec O' A))) (double (cons (vec O' A) (vec O' B))))); auto.
apply compatible; auto.
apply transitive with (plus (double (cons (vec O' B) (vec O' A))) (plus zero (double (cons (vec O' A) (vec O' B))))); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (double (cons (vec O' B) (vec O' A))) (double (cons (vec O' A) (vec O' B)))); auto.
apply compatible; auto.
apply transitive with (double (plus (cons (vec O' B) (vec O' A)) (cons (vec O' A) (vec O' B)))); auto.
apply transitive with (double zero); auto.
apply unicite_perpendiculaire with (u := vec A T) (u' := vec A T'); auto.
apply tangente_reciproque with (B := B) (O := O); auto.
unfold orthogonal in |- *.
apply transitive with (double (cons u (vec O A))); auto.
apply R_double; auto.
apply vR_R_compatible; auto.
apply transitive with (cons (vec O' A) (vec O' B)); auto.
apply tangente; auto.
unfold orthogonal in |- *.
apply transitive with (double (cons v (vec O' A))); auto.
apply R_double; auto.
apply vR_R_compatible; auto.
unfold orthogonal in |- *.
apply transitive with (double (cons u (vec O A))); auto.
apply R_double; auto.
apply vR_R_compatible; auto.
unfold orthogonal in |- *.
apply transitive with (double (cons v (vec O' A))); auto.
apply R_double; auto.
apply vR_R_compatible; auto.
apply transitive with (double (cons (vec M A) (vec M B))); auto.
apply symetrique; apply angle_inscrit; auto.
apply transitive with (double (cons (vec M' A) (vec M' B))); auto.
apply angle_inscrit; auto.
unfold not, colineaire in |- *; intros.
apply H.
unfold colineaire in |- *.
apply transitive with (double (cons (vec M' A) (vec M' B))); auto.

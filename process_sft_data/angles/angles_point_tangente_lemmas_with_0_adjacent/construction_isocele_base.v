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

Lemma construction_isocele_base : forall (A B : PO) (a : AV), exists u : V, (exists v : V, R (cons (vec A B) u) (cons v (vec B A)) /\ R (cons u v) (double a)).
intros A B a; try assumption.
elim exists_opp_angle with (a := a); intros a' H; try exact H.
elim angle_cons with (a := plus pisurdeux a') (u := vec A B); intros u H2; try exact H2.
elim angle_cons with (a := cons u (vec A B)) (u := vec B A); intros v H3; try exact H3.
exists u.
exists v.
split; [ try assumption | idtac ].
auto.
apply transitive with (plus (cons u (vec A B)) (plus (cons (vec A B) (vec B A)) (cons (vec B A) v))); auto.
apply transitive with (plus (cons u (vec A B)) (plus pi (cons (vec B A) v))); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (cons (vec A B) (opp (vec A B))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply transitive with (plus (cons u (vec A B)) (plus (cons (vec B A) v) pi)); auto.
apply compatible; auto.
apply transitive with (plus (cons u (vec A B)) (plus (cons u (vec A B)) pi)); auto.
apply compatible; auto.
apply compatible; auto.
apply regulier with (a := plus (plus pisurdeux a') (plus pisurdeux a')) (c := plus (plus pisurdeux a') (plus pisurdeux a')); auto.
apply transitive with (plus (plus (cons (vec A B) u) (cons (vec A B) u)) (plus (cons u (vec A B)) (plus (cons u (vec A B)) pi))); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus (cons (vec A B) u) (cons (vec A B) u)) (plus (plus (cons u (vec A B)) (cons u (vec A B))) pi)); auto.
apply compatible; auto.
apply transitive with (plus (plus (plus (cons (vec A B) u) (cons (vec A B) u)) (plus (cons u (vec A B)) (cons u (vec A B)))) pi); auto.
apply transitive with (plus (plus (plus (cons (vec A B) u) (cons u (vec A B))) (plus (cons (vec A B) u) (cons u (vec A B)))) pi); auto.
apply compatible; auto.
apply calcul4.
apply transitive with (plus (plus (cons (vec A B) (vec A B)) (cons (vec A B) (vec A B))) pi); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus zero zero) pi); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus (plus a a') (plus a a')) pi); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus (plus a a) (plus a' a')) pi); auto.
apply compatible; auto.
apply calcul4.
apply transitive with (plus (plus (double a) (plus a' a')) pi); auto.
apply transitive with (plus (double a) (plus (plus a' a') pi)); auto.
apply transitive with (plus (plus (plus a' a') pi) (double a)); auto.
apply compatible; auto.
apply transitive with (plus (plus a' a') (plus pisurdeux pisurdeux)); auto.
apply compatible; auto.
apply transitive with (plus (plus pisurdeux pisurdeux) (plus a' a')); auto.
apply calcul4.

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
Axiom cocyclicite_six : forall A B C D : PO, sont_cocycliques C A B D -> ex (fun O : PO => (circonscrit C A B O /\ circonscrit D A B O) /\ isocele O C D).
Axiom non_zero_pi : ~ R pi zero.

Theorem reciproque_cocyclique : forall M A B M' : PO, ~ colineaire (vec M A) (vec M B) -> R (double (cons (vec M' A) (vec M' B))) (double (cons (vec M A) (vec M B))) -> sont_cocycliques M A B M'.
unfold sont_cocycliques in |- *.
intros M A B M' H H0; try assumption.
elim construction_circonscrit with (M := M) (A := A) (B := B); [ intros O H2; try exact H2 | idtac ].
exists O.
elim construction_circonscrit with (M := M') (A := A) (B := B); [ intros O' H1; try exact H1 | idtac ].
exists O'.
split; [ split; [ idtac | try assumption ] | idtac ].
try exact H2.
elim H1; intros H3 H4; elim H4; intros H5 H6; clear H4 H1; try exact H5.
elim H2; intros H1 H4; elim H4; intros H7 H8; clear H4 H2; try exact H7.
cut (R (cons (vec O A) (vec O B)) (cons (vec O' A) (vec O' B))); intros.
cut (R (double (cons (vec A B) (vec A O))) (double (cons (vec A B) (vec A O')))); intros.
cut (R (double (cons (vec B O) (vec B A))) (double (cons (vec B O') (vec B A)))); intros.
unfold colineaire in |- *.
split; [ try assumption | idtac ].
apply transitive with (double (cons (vec A O) (vec A O'))); auto.
apply transitive with (double (cons (opp (vec O A)) (opp (vec O' A)))); auto.
apply R_double.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
apply transitive with (double (plus (cons (vec A O) (vec A B)) (cons (vec A B) (vec A O')))); auto.
apply transitive with (plus (double (cons (vec A O) (vec A B))) (double (cons (vec A B) (vec A O')))); auto.
apply transitive with (plus (double (cons (vec A O) (vec A B))) (double (cons (vec A B) (vec A O)))); auto.
apply compatible; auto.
apply transitive with (double (plus (cons (vec A O) (vec A B)) (cons (vec A B) (vec A O)))); auto.
apply transitive with (double zero); auto.
apply transitive with (double (cons (vec B O) (vec B O'))); auto.
apply transitive with (double (cons (opp (vec O B)) (opp (vec O' B)))); auto.
apply R_double.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
apply transitive with (double (plus (cons (vec B O) (vec B A)) (cons (vec B A) (vec B O')))); auto.
apply transitive with (plus (double (cons (vec B O) (vec B A))) (double (cons (vec B A) (vec B O')))); auto.
apply transitive with (plus (double (cons (vec B O') (vec B A))) (double (cons (vec B A) (vec B O')))); auto.
apply compatible; auto.
apply transitive with (double (plus (cons (vec B O') (vec B A)) (cons (vec B A) (vec B O')))); auto.
apply transitive with (double zero); auto.
generalize (triangle_isocele (A:=O) (B:=A) (C:=B)); intros.
apply regulier with (a := cons (vec O A) (vec O B)) (c := cons (vec O' A) (vec O' B)); auto.
apply transitive with (plus (cons (vec O A) (vec O B)) (double (cons (vec A B) (vec A O)))); auto.
apply compatible; auto.
apply transitive with pi; auto.
generalize (triangle_isocele (A:=O') (B:=A) (C:=B)); intros.
apply symetrique; auto.
apply transitive with (plus (cons (vec O' A) (vec O' B)) (double (cons (vec A B) (vec A O')))); auto.
apply compatible; auto.
generalize (triangle_isocele (A:=O) (B:=A) (C:=B)); intros.
apply regulier with (a := cons (vec O A) (vec O B)) (c := cons (vec O' A) (vec O' B)); auto.
apply transitive with pi; auto.
generalize (triangle_isocele (A:=O') (B:=A) (C:=B)); intros.
apply symetrique; auto.
apply transitive with (double (cons (vec M A) (vec M B))); auto.
apply symetrique; apply angle_inscrit; auto.
try exact H6.
generalize (triangle_isocele (A:=O') (B:=A) (C:=B)); intros.
apply transitive with (double (cons (vec M' A) (vec M' B))); auto.
apply angle_inscrit; auto.
unfold colineaire in H.
unfold colineaire, not in |- *.
intros H1; try assumption.
apply H.
apply transitive with (double (cons (vec M' A) (vec M' B))); auto.
try exact H.

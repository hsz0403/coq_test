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

Lemma changement_base_cocyclique_2 : forall A B C D : PO, ~ colineaire (vec C A) (vec C B) -> R (double (cons (vec C A) (vec C B))) (double (cons (vec D A) (vec D B))) -> R (double (cons (vec B C) (vec B A))) (double (cons (vec D C) (vec D A))).
intros A B C D H H0; try assumption.
cut (ex (fun O : PO => (circonscrit C A B O /\ circonscrit D A B O) /\ isocele O C D)); intros.
unfold circonscrit in H1.
elim H1; intros O H2; elim H2; intros H3 H4; elim H3; intros H5 H6; elim H5; intros H7 H8; elim H8; intros H9 H10; clear H8 H5 H3 H2 H1; try exact H9.
elim H6; intros H1 H2; elim H2; intros H3 H5; clear H2 H6; try exact H3.
apply (cocyclique (M:=D) (A:=C) (B:=A) (O:=O) (M':=B)); auto.
apply cocyclicite_six.
apply reciproque_cocyclique; auto.

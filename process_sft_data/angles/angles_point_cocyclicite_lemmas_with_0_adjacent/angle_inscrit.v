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

Theorem angle_inscrit : forall A B M O : PO, isocele O M A -> isocele O M B -> R (double (cons (vec M A) (vec M B))) (cons (vec O A) (vec O B)).
intros A B M O H H0; try assumption.
unfold double in |- *.
lapply (triangle_isocele (A:=O) (B:=M) (C:=B)); intros.
lapply (isocele_permute (A:=O) (B:=M) (C:=A)); intros.
cut (R (plus (cons (vec O A) (vec O B)) (plus (cons (vec M B) (vec M A)) (cons (vec M B) (vec M A)))) (plus pi pi)).
intros.
apply transitive with (plus (plus (cons (vec O A) (vec O B)) (plus (cons (vec M B) (vec M A)) (cons (vec M B) (vec M A)))) (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply transitive with (plus zero (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply symetrique.
apply zero_plus_a.
apply transitive with (plus (plus pi pi) (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply compatible.
apply symetrique.
apply pi_plus_pi.
apply reflexive.
apply transitive with (plus (plus pi pi) (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply compatible.
apply reflexive.
apply reflexive.
apply compatible.
apply symetrique.
try exact H3.
apply reflexive.
apply transitive with (plus (cons (vec O A) (vec O B)) (plus (plus (cons (vec M B) (vec M A)) (cons (vec M B) (vec M A))) (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B))))).
apply symetrique.
apply point_angle.plus_assoc.
apply transitive with (plus (cons (vec O A) (vec O B)) zero).
apply compatible.
apply reflexive.
apply transitive with (plus (plus (cons (vec M B) (vec M A)) (cons (vec M A) (vec M B))) (plus (cons (vec M B) (vec M A)) (cons (vec M A) (vec M B)))).
apply calcul4.
apply transitive with (plus zero zero).
apply compatible.
apply permute.
apply permute.
apply zero_plus_a.
apply plus_zero.
apply transitive with (plus (plus (cons (vec O A) (vec O M)) (cons (vec O M) (vec O B))) (plus (plus (cons (vec M O) (vec M A)) (cons (vec M B) (vec M O))) (plus (cons (vec M O) (vec M A)) (cons (vec M B) (vec M O))))).
apply compatible.
apply symetrique.
apply Chasles.
apply compatible.
apply symetrique.
apply transitive with (plus (cons (vec M B) (vec M O)) (cons (vec M O) (vec M A))).
apply plus_sym.
apply Chasles.
apply symetrique.
apply transitive with (plus (cons (vec M B) (vec M O)) (cons (vec M O) (vec M A))).
apply plus_sym.
apply Chasles.
apply transitive with (plus (plus (cons (vec O A) (vec O M)) (plus (cons (vec M O) (vec M A)) (cons (vec M O) (vec M A)))) (plus (cons (vec O M) (vec O B)) (plus (cons (vec M B) (vec M O)) (cons (vec M B) (vec M O))))).
apply symetrique.
apply calcul3.
apply compatible.
try exact H2.
try exact H1.
try exact H.
try exact H0.

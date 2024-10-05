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

Theorem tangente_reciproque : forall A B O T T' : PO, isocele O A B -> orthogonal (vec A T) (vec O A) -> R (double (cons (vec A T') (vec A B))) (cons (vec O A) (vec O B)) -> colineaire (vec A T) (vec A T').
unfold orthogonal in |- *.
intros A B O T T' H H0 H1; try assumption.
unfold colineaire in |- *.
lapply (tangente (A:=A) (B:=B) (O:=O) (T:=T)); auto.
intros H2; try assumption.
apply transitive with (double (plus (cons (vec A T) (vec A B)) (cons (vec A B) (vec A T')))); auto.
unfold double in |- *.
apply transitive with (plus (plus (cons (vec A T) (vec A B)) (cons (vec A T) (vec A B))) (plus (cons (vec A B) (vec A T')) (cons (vec A B) (vec A T')))); auto.
apply calcul4.
apply transitive with (plus (cons (vec O A) (vec O B)) (cons (vec O B) (vec O A))).
apply compatible; auto.
apply transitive with (double (cons (vec A B) (vec A T'))); auto.
apply regulier with (a := double (cons (vec A T') (vec A B))) (c := cons (vec O A) (vec O B)); auto.
apply transitive with (double (plus (cons (vec A T') (vec A B)) (cons (vec A B) (vec A T')))); auto.
apply transitive with (double (cons (vec A T') (vec A T'))); auto.
apply transitive with (plus zero zero); auto.
unfold double in |- *.
apply compatible; auto.
apply transitive with zero; auto.
apply transitive with (cons (vec O A) (vec O A)); auto.

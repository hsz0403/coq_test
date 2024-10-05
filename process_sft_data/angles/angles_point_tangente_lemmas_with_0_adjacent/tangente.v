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

Theorem tangente : forall A B O T : PO, isocele O A B -> orthogonal (vec A T) (vec O A) -> R (double (cons (vec A T) (vec A B))) (cons (vec O A) (vec O B)).
unfold double, orthogonal in |- *.
intros A B O T H H0; try assumption.
apply transitive with (plus (plus (cons (vec A T) (vec O A)) (cons (vec O A) (vec A B))) (plus (cons (vec A T) (vec O A)) (cons (vec O A) (vec A B)))); auto.
apply compatible; auto.
apply transitive with (plus (plus (cons (vec A T) (vec O A)) (cons (vec A T) (vec O A))) (plus (cons (vec O A) (vec A B)) (cons (vec O A) (vec A B)))); auto.
apply calcul4.
apply transitive with (plus pi (plus (cons (vec O A) (vec A B)) (cons (vec O A) (vec A B)))); auto.
apply compatible; auto.
lapply (triangle_isocele (A:=O) (B:=A) (C:=B)).
intros H1; try assumption.
apply transitive with (plus (plus (cons (vec O A) (vec O B)) (plus (cons (vec A B) (vec A O)) (cons (vec A B) (vec A O)))) (plus (cons (vec O A) (vec A B)) (cons (vec O A) (vec A B)))); auto.
apply compatible; auto.
apply transitive with (plus (cons (vec O A) (vec O B)) (plus (plus (cons (vec A B) (vec A O)) (cons (vec A B) (vec A O))) (plus (cons (vec O A) (vec A B)) (cons (vec O A) (vec A B))))); auto.
apply transitive with (plus (cons (vec O A) (vec O B)) (plus (plus (cons (vec A B) (vec A O)) (cons (vec O A) (vec A B))) (plus (cons (vec A B) (vec A O)) (cons (vec O A) (vec A B))))); auto.
apply compatible; auto.
apply calcul4.
apply transitive with (plus (cons (vec O A) (vec O B)) (plus pi pi)); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (cons (vec O A) (vec A B)) (cons (vec A B) (vec A O))); auto.
apply transitive with (cons (vec O A) (vec A O)); auto.
apply transitive with (cons (vec O A) (opp (vec O A))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply transitive with (plus (cons (vec O A) (vec A B)) (cons (vec A B) (vec A O))); auto.
apply transitive with (cons (vec O A) (vec A O)); auto.
apply transitive with (cons (vec O A) (opp (vec O A))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply transitive with (plus (cons (vec O A) (vec O B)) zero).
apply compatible; auto.
apply plus_zero.
try exact H.

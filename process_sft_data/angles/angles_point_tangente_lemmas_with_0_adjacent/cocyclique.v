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

Theorem cocyclique : forall M A B O M' : PO, isocele O A B -> isocele O M A -> isocele O M B -> isocele O M' A -> isocele O M' B -> R (double (cons (vec M' A) (vec M' B))) (double (cons (vec M A) (vec M B))).
intros M A B O M' H H0 H1 H2 H3; try assumption.
apply transitive with (cons (vec O A) (vec O B)).
apply angle_inscrit; auto.
apply symetrique; apply angle_inscrit; auto.

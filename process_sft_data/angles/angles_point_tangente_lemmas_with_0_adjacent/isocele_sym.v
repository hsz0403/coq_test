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

Lemma isocele_sym : forall A B C : PO, isocele A B C -> isocele A C B.
unfold isocele in |- *; intros.
apply transitive with (plus (cons (vec C B) (vec A B)) (cons (vec A B) (vec C A))); auto.
apply transitive with (plus (cons (vec C A) (vec C B)) (cons (vec A B) (vec C A))); auto.
apply compatible; auto.
apply transitive with (cons (vec B C) (vec B A)); auto.
apply transitive with (cons (opp (vec C B)) (opp (vec A B))); auto.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
apply transitive with (plus (cons (vec A B) (vec C A)) (cons (vec C A) (vec C B))); auto.
apply transitive with (cons (vec A B) (vec C B)); auto.
apply transitive with (cons (opp (vec B A)) (opp (vec B C))); auto.
apply symetrique.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.

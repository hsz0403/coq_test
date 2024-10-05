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

Lemma deux_rectangles : forall A B C D : PO, orthogonal (vec C A) (vec C B) -> orthogonal (vec D A) (vec D B) -> R (double (cons (vec B C) (vec B A))) (double (cons (vec D C) (vec D A))).
unfold orthogonal in |- *; intros A B C D H H0; try assumption.
apply changement_base_cocyclique_2.
unfold not, colineaire in |- *.
intros H1; try assumption.
apply non_zero_pi.
apply transitive with (double (cons (vec C A) (vec C B))); auto.
apply transitive with pi; auto.

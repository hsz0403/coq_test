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

Lemma calcul5 : forall a b c d : AV, R (plus (plus a (plus b c)) (plus d d)) (plus a (plus (plus d b) (plus d c))).
intros a b c d; try assumption.
apply transitive with (plus a (plus (plus b c) (plus d d))); auto.
apply compatible; auto.
apply transitive with (plus (plus b d) (plus c d)); auto.
apply calcul4.
apply compatible; auto.

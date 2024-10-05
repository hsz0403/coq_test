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

Lemma calcul4 : forall a b c d : AV, R (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
intros a b c d; try assumption.
apply transitive with (plus (plus (plus a b) c) d); auto.
apply transitive with (plus (plus (plus a c) b) d); auto.
apply compatible; auto.
apply transitive with (plus a (plus b c)); auto.
apply transitive with (plus a (plus c b)); auto.
apply compatible; auto.

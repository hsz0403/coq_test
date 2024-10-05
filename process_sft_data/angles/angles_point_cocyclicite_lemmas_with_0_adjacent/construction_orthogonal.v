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

Lemma construction_orthogonal : forall u : V, exists v : V, orthogonal v u.
intros u; try assumption.
cut (exists v : V, R (double (cons u v)) pi).
intros H; try assumption.
elim H; intros v H0; clear H; try exact H0.
exists v.
auto.
elim angle_cons with (a := pisurdeux) (u := u); intros v H0; try exact H0.
exists v.
apply transitive with (double pisurdeux).
auto.
auto.

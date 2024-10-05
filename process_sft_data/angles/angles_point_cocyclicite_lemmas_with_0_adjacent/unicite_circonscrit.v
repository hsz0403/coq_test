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

Lemma unicite_circonscrit : forall M A B O O' : PO, isocele O A B -> isocele O M B -> isocele O M A -> isocele O' A B -> isocele O' M B -> isocele O' M A -> (colineaire (vec O A) (vec O' A) /\ colineaire (vec O B) (vec O' B)) /\ colineaire (vec O M) (vec O' M).
unfold colineaire in |- *.
intros M A B O O' H H0 H1 H2 H3 H4.
cut (R (cons (vec O A) (vec O B)) (cons (vec O' A) (vec O' B))); intros.
cut (R (double (cons (vec A B) (vec A O))) (double (cons (vec A B) (vec A O')))); intros.
cut (R (double (cons (vec B O) (vec B A))) (double (cons (vec B O') (vec B A)))); intros.
split; [ idtac | try assumption ].
split; [ idtac | try assumption ].
apply transitive with (double (cons (opp (vec O A)) (opp (vec O' A)))); auto.
apply transitive with (double (plus (cons (opp (vec O A)) (vec A B)) (cons (vec A B) (opp (vec O' A))))); auto.
apply transitive with (double (plus (cons (opp (vec O A)) (vec A B)) (cons (vec A B) (opp (vec O' A))))); auto.
apply transitive with (plus (double (cons (opp (vec O A)) (vec A B))) (double (cons (vec A B) (opp (vec O' A))))); auto.
apply transitive with (plus (double (cons (opp (vec O A)) (vec A B))) (double (cons (vec A B) (vec A O)))); auto.
apply compatible; auto.
apply transitive with (double (cons (vec A B) (vec A O'))); auto.
apply R_double.
apply vR_R_compatible; auto.
apply opp_vect.
apply transitive with (double (plus (cons (opp (vec O A)) (vec A B)) (cons (vec A B) (vec A O)))); auto.
apply transitive with (double (plus (cons (vec A O) (vec A B)) (cons (vec A B) (vec A O)))); auto.
apply R_double.
apply compatible; auto.
apply vR_R_compatible; auto.
apply opp_vect.
apply transitive with (double zero); auto.
apply transitive with (double (cons (vec B O) (vec B O'))); auto.
apply R_double.
apply transitive with (cons (opp (vec B O)) (opp (vec B O'))); auto.
apply transitive with (cons (opp (vec B O)) (opp (vec B O'))); auto.
apply symetrique; auto.
apply symetrique; auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply v_sym; apply opp_vect.
apply transitive with (double (plus (cons (vec B O) (vec B A)) (cons (vec B A) (vec B O')))); auto.
apply transitive with (plus (double (cons (vec B O) (vec B A))) (double (cons (vec B A) (vec B O')))); auto.
apply transitive with (plus (double (cons (vec B O) (vec B A))) (double (cons (vec B A) (vec B O)))); auto.
apply compatible; auto.
apply transitive with (double (plus (cons (vec B O) (vec B A)) (cons (vec B A) (vec B O)))); auto.
apply transitive with (double zero); auto.
apply transitive with (double (cons (vec M O) (vec M O'))); auto.
apply R_double.
apply transitive with (cons (opp (vec M O)) (opp (vec M O'))); auto.
apply symetrique; auto.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
apply transitive with (double (plus (cons (vec M O) (vec M A)) (cons (vec M A) (vec M O')))); auto.
apply transitive with (plus (double (cons (vec M O) (vec M A))) (double (cons (vec M A) (vec M O')))); auto.
apply transitive with (double (plus (cons (vec M O) (vec M A)) (cons (vec M A) (vec M O')))); auto.
apply transitive with (plus (double (cons (vec M O) (vec M A))) (double (cons (vec M A) (vec M O')))); auto.
apply transitive with (plus (double (cons (vec A M) (vec A O))) (double (cons (vec A O') (vec A M)))); auto.
apply compatible; auto.
apply transitive with (double (plus (cons (vec A M) (vec A O)) (cons (vec A O') (vec A M)))); auto.
apply transitive with (double (cons (vec A O') (vec A O))); auto.
apply R_double.
apply transitive with (plus (cons (vec A O') (vec A M)) (cons (vec A M) (vec A O))); auto.
cut (R (double (cons (vec A O) (vec A O'))) zero); intros.
apply regulier with (a := double (cons (vec A O) (vec A O'))) (c := zero); auto.
apply transitive with (double (plus (cons (vec A O) (vec A O')) (cons (vec A O') (vec A O)))); auto.
apply transitive with (double zero); auto.
apply transitive with (double (plus (cons (vec A O) (vec A B)) (cons (vec A B) (vec A O')))); auto.
apply transitive with (plus (double (cons (vec A O) (vec A B))) (double (cons (vec A B) (vec A O')))); auto.
apply transitive with (plus (double (cons (vec A O) (vec A B))) (double (cons (vec A B) (vec A O)))); auto.
apply compatible; auto.
apply transitive with (double (plus (cons (vec A O) (vec A B)) (cons (vec A B) (vec A O)))); auto.
apply transitive with (double zero); auto.
apply transitive with (double (cons (vec A B) (vec A O))); auto.
apply transitive with (double (cons (vec A B) (vec A O'))); auto.
generalize (triangle_isocele (A:=O) (B:=A) (C:=B)); intros.
apply regulier with (a := cons (vec O A) (vec O B)) (c := cons (vec O' A) (vec O' B)); auto.
apply transitive with pi; auto.
generalize (triangle_isocele (A:=O') (B:=A) (C:=B)); intros.
apply symetrique; auto.
apply transitive with (double (cons (vec M A) (vec M B))); auto.
apply symetrique; apply angle_inscrit; auto.
auto.
apply angle_inscrit; auto.

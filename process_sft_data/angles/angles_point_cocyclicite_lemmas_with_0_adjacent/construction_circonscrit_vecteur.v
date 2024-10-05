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

Lemma construction_circonscrit_vecteur : forall M A B : PO, ex (fun u : V => ex (fun v : V => ex (fun w : V => (R (cons u v) (double (cons (vec M A) (vec M B))) /\ R (cons u w) (double (cons (vec B A) (vec B M))) /\ R (cons v w) (double (cons (vec A B) (vec A M)))) /\ R (cons (vec A B) u) (cons v (vec B A)) /\ R (cons w (vec M B)) (cons (vec B M) v) /\ R (cons (vec M A) w) (cons u (vec A M))))).
intros M A B; try assumption.
elim construction_isocele_base with (A := A) (B := B) (a := cons (vec M A) (vec M B)); intros u H; elim H; intros v H0; clear H; try exact H0.
elim H0; intros H H1; clear H0; try exact H1.
exists u; exists v.
elim angle_cons with (a := cons u (vec A M)) (u := vec M A); intros w H'; try exact H'.
exists w.
generalize (somme_triangle M A B).
generalize (somme_pi (vec A B) u v).
intros H2 H3; try assumption.
split; [ split; try assumption | try assumption ].
cut (R (cons u w) (double (cons (vec B A) (vec B M)))); intros.
split; [ try assumption | idtac ].
apply regulier with (a := cons u v) (c := double (cons (vec M A) (vec M B))); auto.
apply transitive with (cons u w); auto.
apply transitive with (double (cons (vec B A) (vec B M))); auto.
apply regulier with (a := double (cons (vec B M) (vec B A))) (c := double (cons (vec B M) (vec B A))); auto.
apply transitive with (plus (plus (double (cons (vec M A) (vec M B))) (double (cons (vec A B) (vec A M)))) (double (cons (vec B M) (vec B A)))); auto.
apply transitive with (plus (double (cons (vec M A) (vec M B))) (plus (double (cons (vec A B) (vec A M))) (double (cons (vec B M) (vec B A))))); auto.
apply transitive with (plus (double (cons (vec M A) (vec M B))) (double (plus (cons (vec A B) (vec A M)) (cons (vec B M) (vec B A))))); auto.
apply transitive with (double (plus (cons (vec M A) (vec M B)) (plus (cons (vec A B) (vec A M)) (cons (vec B M) (vec B A))))); auto.
apply transitive with (double (plus (cons (vec B M) (vec B A)) (cons (vec B A) (vec B M)))); auto.
apply transitive with (double pi); auto.
apply transitive with (double (cons (vec B M) (vec B M))); auto.
apply transitive with (double zero); auto.
apply transitive with zero; auto.
apply compatible; auto.
apply transitive with (plus (cons u (vec A M)) (plus (cons (vec A M) (vec M A)) (cons (vec M A) w))); auto.
apply transitive with (plus (cons u (vec A M)) (plus pi (cons (vec M A) w))); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (cons u (vec A M)) (plus (cons (vec M A) w) pi)); auto.
apply compatible; auto.
apply transitive with (plus (plus (cons u (vec A M)) (cons (vec M A) w)) pi); auto.
apply transitive with (plus (plus (cons u (vec A M)) (cons u (vec A M))) pi); auto.
apply compatible; auto.
apply compatible; auto.
apply regulier with (a := plus (cons (vec A B) u) (cons (vec A B) u)) (c := plus (cons (vec A B) u) (cons (vec A B) u)); auto.
apply transitive with (plus (plus (plus (cons (vec A B) u) (cons (vec A B) u)) (plus (cons u (vec A M)) (cons u (vec A M)))) pi); auto.
apply transitive with (plus (plus (plus (cons (vec A B) u) (cons u (vec A M))) (plus (cons (vec A B) u) (cons u (vec A M)))) pi); auto.
apply compatible; auto.
apply calcul4; auto.
apply transitive with (plus (plus (cons (vec A B) (vec A M)) (cons (vec A B) (vec A M))) pi); auto.
apply compatible; auto.
apply compatible; auto.
apply regulier with (a := cons u v) (c := cons u v); auto.
apply transitive with (plus (plus (cons u v) (plus (cons (vec A B) u) (cons (vec A B) u))) (double (cons (vec B A) (vec B M)))); auto.
apply transitive with (plus pi (double (cons (vec B A) (vec B M)))); auto.
apply transitive with (plus (plus (cons u v) (plus (cons (vec A B) (vec A M)) (cons (vec A B) (vec A M)))) pi); auto.
apply transitive with (plus (double (cons (vec B A) (vec B M))) pi); auto.
apply compatible; auto.
apply transitive with (plus (double (cons (vec M A) (vec M B))) (double (cons (vec A B) (vec A M)))); auto.
apply compatible; auto.
apply regulier with (a := double (cons (vec B M) (vec B A))) (c := double (cons (vec B M) (vec B A))); auto.
apply transitive with (plus (plus (double (cons (vec M A) (vec M B))) (double (cons (vec A B) (vec A M)))) (double (cons (vec B M) (vec B A)))); auto.
apply transitive with (plus (double (cons (vec M A) (vec M B))) (plus (double (cons (vec A B) (vec A M))) (double (cons (vec B M) (vec B A))))); auto.
apply transitive with (plus (double (cons (vec M A) (vec M B))) (double (plus (cons (vec A B) (vec A M)) (cons (vec B M) (vec B A))))); auto.
apply compatible; auto.
apply transitive with (double (plus (cons (vec M A) (vec M B)) (plus (cons (vec A B) (vec A M)) (cons (vec B M) (vec B A))))); auto.
apply transitive with (double (plus (cons (vec B M) (vec B A)) (cons (vec B A) (vec B M)))); auto.
apply transitive with (double pi); auto.
apply transitive with (double (cons (vec B M) (vec B M))); auto.
apply transitive with (double zero); auto.
apply transitive with zero; auto.
apply compatible; auto.
apply transitive with (plus (cons (vec A B) u) (plus (cons v (opp (vec A B))) (cons (opp u) (opp v)))); auto.
apply transitive with (plus (plus (cons (vec A B) u) (cons (vec A B) u)) (cons u v)); auto.
apply transitive with (plus (plus (cons (vec A B) u) (cons v (opp (vec A B)))) (cons (opp u) (opp v))); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (cons v (vec B A)); auto.
apply vR_R_compatible; auto.
apply opp_vect; auto.
split; [ try assumption | idtac ].
split; [ try assumption | idtac ].
apply regulier with (a := cons (vec M A) w) (c := cons u (vec A M)); auto.
apply transitive with (cons (vec M A) (vec M B)); auto.
apply transitive with (plus (cons u (vec A M)) (plus (cons (vec B M) (vec B A)) (cons (vec B A) v))); auto.
apply transitive with (plus (cons u (vec A M)) (plus (cons (vec B M) (vec B A)) (cons u (vec A B)))); auto.
apply transitive with (plus (cons u (vec A M)) (plus (cons u (vec A B)) (cons (vec B M) (vec B A)))); auto.
apply transitive with (plus (plus (cons u (vec A B)) (cons (vec A B) (vec A M))) (plus (cons u (vec A B)) (cons (vec B M) (vec B A)))); auto.
apply regulier with (a := cons (vec M A) (vec M B)) (c := cons (vec M A) (vec M B)); auto.
apply transitive with (plus (plus (cons (vec M A) (vec M B)) (plus (cons (vec A B) (vec A M)) (cons (vec B M) (vec B A)))) (plus (cons u (vec A B)) (cons u (vec A B)))); auto.
apply transitive with (plus pi (plus (cons u (vec A B)) (cons u (vec A B)))); auto.
apply transitive with (cons u v); auto.
apply regulier with (a := plus (cons (vec A B) u) (cons (vec A B) u)) (c := plus (cons (vec A B) u) (cons (vec A B) u)); auto.
apply transitive with pi; auto.
apply transitive with (plus (plus (cons (vec A B) u) (cons v (vec B A))) (cons u v)); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (cons (vec A B) u) (plus (cons v (vec B A)) (cons u v))); auto.
apply transitive with (plus (cons (vec A B) u) (plus (cons v (opp (vec A B))) (cons (opp u) (opp v)))); auto.
apply compatible; auto.
apply compatible; auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply transitive with (plus (plus pi (plus (cons u (vec A B)) (cons u (vec A B)))) (plus (cons (vec A B) u) (cons (vec A B) u))); auto.
apply transitive with (plus pi (plus (plus (cons u (vec A B)) (cons u (vec A B))) (plus (cons (vec A B) u) (cons (vec A B) u)))); auto.
apply transitive with (plus zero pi); auto.
apply transitive with (plus pi zero); auto.
apply compatible; auto.
apply transitive with (plus (plus (cons u (vec A B)) (cons (vec A B) u)) (plus (cons u (vec A B)) (cons (vec A B) u))); auto.
apply transitive with (plus (cons u u) (cons u u)); auto.
apply compatible; auto.
apply calcul4; auto.
apply compatible; auto.
apply calcul5; auto.
apply compatible; auto.
apply compatible; auto.
apply compatible; auto.
apply compatible; auto.
apply compatible; auto.
apply symetrique; auto.

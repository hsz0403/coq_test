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

Lemma calcul4 : forall a b c d : AV, R (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
intros a b c d; try assumption.
apply transitive with (plus (plus (plus a b) c) d); auto.
apply transitive with (plus (plus (plus a c) b) d); auto.
apply compatible; auto.
apply transitive with (plus a (plus b c)); auto.
apply transitive with (plus a (plus c b)); auto.
Admitted.

Theorem angle_inscrit : forall A B M O : PO, isocele O M A -> isocele O M B -> R (double (cons (vec M A) (vec M B))) (cons (vec O A) (vec O B)).
intros A B M O H H0; try assumption.
unfold double in |- *.
lapply (triangle_isocele (A:=O) (B:=M) (C:=B)); intros.
lapply (isocele_permute (A:=O) (B:=M) (C:=A)); intros.
cut (R (plus (cons (vec O A) (vec O B)) (plus (cons (vec M B) (vec M A)) (cons (vec M B) (vec M A)))) (plus pi pi)).
intros.
apply transitive with (plus (plus (cons (vec O A) (vec O B)) (plus (cons (vec M B) (vec M A)) (cons (vec M B) (vec M A)))) (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply transitive with (plus zero (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply symetrique.
apply zero_plus_a.
apply transitive with (plus (plus pi pi) (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply compatible.
apply symetrique.
apply pi_plus_pi.
apply reflexive.
apply transitive with (plus (plus pi pi) (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B)))).
apply compatible.
apply reflexive.
apply reflexive.
apply compatible.
apply symetrique.
try exact H3.
apply reflexive.
apply transitive with (plus (cons (vec O A) (vec O B)) (plus (plus (cons (vec M B) (vec M A)) (cons (vec M B) (vec M A))) (plus (cons (vec M A) (vec M B)) (cons (vec M A) (vec M B))))).
apply symetrique.
apply point_angle.plus_assoc.
apply transitive with (plus (cons (vec O A) (vec O B)) zero).
apply compatible.
apply reflexive.
apply transitive with (plus (plus (cons (vec M B) (vec M A)) (cons (vec M A) (vec M B))) (plus (cons (vec M B) (vec M A)) (cons (vec M A) (vec M B)))).
apply calcul4.
apply transitive with (plus zero zero).
apply compatible.
apply permute.
apply permute.
apply zero_plus_a.
apply plus_zero.
apply transitive with (plus (plus (cons (vec O A) (vec O M)) (cons (vec O M) (vec O B))) (plus (plus (cons (vec M O) (vec M A)) (cons (vec M B) (vec M O))) (plus (cons (vec M O) (vec M A)) (cons (vec M B) (vec M O))))).
apply compatible.
apply symetrique.
apply Chasles.
apply compatible.
apply symetrique.
apply transitive with (plus (cons (vec M B) (vec M O)) (cons (vec M O) (vec M A))).
apply plus_sym.
apply Chasles.
apply symetrique.
apply transitive with (plus (cons (vec M B) (vec M O)) (cons (vec M O) (vec M A))).
apply plus_sym.
apply Chasles.
apply transitive with (plus (plus (cons (vec O A) (vec O M)) (plus (cons (vec M O) (vec M A)) (cons (vec M O) (vec M A)))) (plus (cons (vec O M) (vec O B)) (plus (cons (vec M B) (vec M O)) (cons (vec M B) (vec M O))))).
apply symetrique.
apply calcul3.
apply compatible.
try exact H2.
try exact H1.
try exact H.
Admitted.

Lemma triangle_rectangle : forall A B M O : PO, isocele O M A -> isocele O M B -> orthogonal (vec M A) (vec M B) -> R (cons (vec O A) (vec O B)) pi.
unfold orthogonal in |- *.
intros A B M O H H0 H1; try assumption.
apply transitive with (double (cons (vec M A) (vec M B))).
apply symetrique; apply angle_inscrit; auto.
Admitted.

Lemma triangle_diametre : forall A B M O : PO, isocele O M A -> isocele O M B -> R (cons (vec O A) (vec O B)) pi -> orthogonal (vec M A) (vec M B).
unfold orthogonal in |- *.
intros A B M O H H0 H1; try assumption.
apply transitive with (cons (vec O A) (vec O B)).
apply angle_inscrit; auto.
Admitted.

Theorem cocyclique : forall M A B O M' : PO, isocele O A B -> isocele O M A -> isocele O M B -> isocele O M' A -> isocele O M' B -> R (double (cons (vec M' A) (vec M' B))) (double (cons (vec M A) (vec M B))).
intros M A B O M' H H0 H1 H2 H3; try assumption.
apply transitive with (cons (vec O A) (vec O B)).
apply angle_inscrit; auto.
Admitted.

Lemma exists_opp_angle : forall a : AV, exists b : AV, R (plus a b) zero.
elim non_vide_V; intros u H; clear H; try exact H.
intros a; try assumption.
elim angle_cons with (a := a) (u := u); intros v H0; try exact H0.
exists (cons v u).
apply transitive with (plus (cons u v) (cons v u)).
apply compatible; auto.
Admitted.

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
Admitted.

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
Admitted.

Lemma abba : forall A B : PO, R (cons (vec A B) (vec B A)) pi.
intros A B; try assumption.
apply transitive with (cons (vec A B) (opp (vec A B))); auto.
apply vR_R_compatible; auto.
Admitted.

Lemma calcul5 : forall a b c d : AV, R (plus (plus a (plus b c)) (plus d d)) (plus a (plus (plus d b) (plus d c))).
intros a b c d; try assumption.
apply transitive with (plus a (plus (plus b c) (plus d d))); auto.
apply compatible; auto.
apply transitive with (plus (plus b d) (plus c d)); auto.
apply calcul4.
Admitted.

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
Admitted.

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
Admitted.

Theorem reciproque_cocyclique : forall M A B M' : PO, ~ colineaire (vec M A) (vec M B) -> R (double (cons (vec M' A) (vec M' B))) (double (cons (vec M A) (vec M B))) -> sont_cocycliques M A B M'.
unfold sont_cocycliques in |- *.
intros M A B M' H H0; try assumption.
elim construction_circonscrit with (M := M) (A := A) (B := B); [ intros O H2; try exact H2 | idtac ].
exists O.
elim construction_circonscrit with (M := M') (A := A) (B := B); [ intros O' H1; try exact H1 | idtac ].
exists O'.
split; [ split; [ idtac | try assumption ] | idtac ].
try exact H2.
elim H1; intros H3 H4; elim H4; intros H5 H6; clear H4 H1; try exact H5.
elim H2; intros H1 H4; elim H4; intros H7 H8; clear H4 H2; try exact H7.
cut (R (cons (vec O A) (vec O B)) (cons (vec O' A) (vec O' B))); intros.
cut (R (double (cons (vec A B) (vec A O))) (double (cons (vec A B) (vec A O')))); intros.
cut (R (double (cons (vec B O) (vec B A))) (double (cons (vec B O') (vec B A)))); intros.
unfold colineaire in |- *.
split; [ try assumption | idtac ].
apply transitive with (double (cons (vec A O) (vec A O'))); auto.
apply transitive with (double (cons (opp (vec O A)) (opp (vec O' A)))); auto.
apply R_double.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
apply transitive with (double (plus (cons (vec A O) (vec A B)) (cons (vec A B) (vec A O')))); auto.
apply transitive with (plus (double (cons (vec A O) (vec A B))) (double (cons (vec A B) (vec A O')))); auto.
apply transitive with (plus (double (cons (vec A O) (vec A B))) (double (cons (vec A B) (vec A O)))); auto.
apply compatible; auto.
apply transitive with (double (plus (cons (vec A O) (vec A B)) (cons (vec A B) (vec A O)))); auto.
apply transitive with (double zero); auto.
apply transitive with (double (cons (vec B O) (vec B O'))); auto.
apply transitive with (double (cons (opp (vec O B)) (opp (vec O' B)))); auto.
apply R_double.
apply vR_R_compatible; auto.
apply opp_vect.
apply opp_vect.
apply transitive with (double (plus (cons (vec B O) (vec B A)) (cons (vec B A) (vec B O')))); auto.
apply transitive with (plus (double (cons (vec B O) (vec B A))) (double (cons (vec B A) (vec B O')))); auto.
apply transitive with (plus (double (cons (vec B O') (vec B A))) (double (cons (vec B A) (vec B O')))); auto.
apply compatible; auto.
apply transitive with (double (plus (cons (vec B O') (vec B A)) (cons (vec B A) (vec B O')))); auto.
apply transitive with (double zero); auto.
generalize (triangle_isocele (A:=O) (B:=A) (C:=B)); intros.
apply regulier with (a := cons (vec O A) (vec O B)) (c := cons (vec O' A) (vec O' B)); auto.
apply transitive with (plus (cons (vec O A) (vec O B)) (double (cons (vec A B) (vec A O)))); auto.
apply compatible; auto.
apply transitive with pi; auto.
generalize (triangle_isocele (A:=O') (B:=A) (C:=B)); intros.
apply symetrique; auto.
apply transitive with (plus (cons (vec O' A) (vec O' B)) (double (cons (vec A B) (vec A O')))); auto.
apply compatible; auto.
generalize (triangle_isocele (A:=O) (B:=A) (C:=B)); intros.
apply regulier with (a := cons (vec O A) (vec O B)) (c := cons (vec O' A) (vec O' B)); auto.
apply transitive with pi; auto.
generalize (triangle_isocele (A:=O') (B:=A) (C:=B)); intros.
apply symetrique; auto.
apply transitive with (double (cons (vec M A) (vec M B))); auto.
apply symetrique; apply angle_inscrit; auto.
try exact H6.
generalize (triangle_isocele (A:=O') (B:=A) (C:=B)); intros.
apply transitive with (double (cons (vec M' A) (vec M' B))); auto.
apply angle_inscrit; auto.
unfold colineaire in H.
unfold colineaire, not in |- *.
intros H1; try assumption.
apply H.
apply transitive with (double (cons (vec M' A) (vec M' B))); auto.
Admitted.

Lemma changement_base_cocyclique : forall A B C D : PO, ~ colineaire (vec C A) (vec C B) -> R (double (cons (vec C A) (vec C B))) (double (cons (vec D A) (vec D B))) -> R (double (cons (vec A C) (vec A D))) (double (cons (vec B C) (vec B D))).
intros A B C D H H0; try assumption.
cut (ex (fun O : PO => (circonscrit C A B O /\ circonscrit D A B O) /\ isocele O C D)); intros.
unfold circonscrit in H1.
elim H1; intros O H2; elim H2; intros H3 H4; elim H3; intros H5 H6; elim H6; intros H7 H8; elim H8; intros H9 H10; clear H8 H6 H3 H2 H1; try exact H10.
elim H5; intros H1 H2; elim H2; intros H3 H6; clear H2 H5; try exact H3.
apply (cocyclique (M:=B) (A:=C) (B:=D) (O:=O) (M':=A)); auto.
apply cocyclicite_six.
Admitted.

Lemma changement_base_cocyclique_2 : forall A B C D : PO, ~ colineaire (vec C A) (vec C B) -> R (double (cons (vec C A) (vec C B))) (double (cons (vec D A) (vec D B))) -> R (double (cons (vec B C) (vec B A))) (double (cons (vec D C) (vec D A))).
intros A B C D H H0; try assumption.
cut (ex (fun O : PO => (circonscrit C A B O /\ circonscrit D A B O) /\ isocele O C D)); intros.
unfold circonscrit in H1.
elim H1; intros O H2; elim H2; intros H3 H4; elim H3; intros H5 H6; elim H5; intros H7 H8; elim H8; intros H9 H10; clear H8 H5 H3 H2 H1; try exact H9.
elim H6; intros H1 H2; elim H2; intros H3 H5; clear H2 H6; try exact H3.
apply (cocyclique (M:=D) (A:=C) (B:=A) (O:=O) (M':=B)); auto.
apply cocyclicite_six.
Admitted.

Lemma deux_rectangles : forall A B C D : PO, orthogonal (vec C A) (vec C B) -> orthogonal (vec D A) (vec D B) -> R (double (cons (vec B C) (vec B A))) (double (cons (vec D C) (vec D A))).
unfold orthogonal in |- *; intros A B C D H H0; try assumption.
apply changement_base_cocyclique_2.
unfold not, colineaire in |- *.
intros H1; try assumption.
apply non_zero_pi.
apply transitive with (double (cons (vec C A) (vec C B))); auto.
Admitted.

Lemma construction_isocele_base : forall (A B : PO) (a : AV), exists u : V, (exists v : V, R (cons (vec A B) u) (cons v (vec B A)) /\ R (cons u v) (double a)).
intros A B a; try assumption.
elim exists_opp_angle with (a := a); intros a' H; try exact H.
elim angle_cons with (a := plus pisurdeux a') (u := vec A B); intros u H2; try exact H2.
elim angle_cons with (a := cons u (vec A B)) (u := vec B A); intros v H3; try exact H3.
exists u.
exists v.
split; [ try assumption | idtac ].
auto.
apply transitive with (plus (cons u (vec A B)) (plus (cons (vec A B) (vec B A)) (cons (vec B A) v))); auto.
apply transitive with (plus (cons u (vec A B)) (plus pi (cons (vec B A) v))); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (cons (vec A B) (opp (vec A B))); auto.
apply vR_R_compatible; auto.
apply v_sym; apply opp_vect.
apply transitive with (plus (cons u (vec A B)) (plus (cons (vec B A) v) pi)); auto.
apply compatible; auto.
apply transitive with (plus (cons u (vec A B)) (plus (cons u (vec A B)) pi)); auto.
apply compatible; auto.
apply compatible; auto.
apply regulier with (a := plus (plus pisurdeux a') (plus pisurdeux a')) (c := plus (plus pisurdeux a') (plus pisurdeux a')); auto.
apply transitive with (plus (plus (cons (vec A B) u) (cons (vec A B) u)) (plus (cons u (vec A B)) (plus (cons u (vec A B)) pi))); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus (cons (vec A B) u) (cons (vec A B) u)) (plus (plus (cons u (vec A B)) (cons u (vec A B))) pi)); auto.
apply compatible; auto.
apply transitive with (plus (plus (plus (cons (vec A B) u) (cons (vec A B) u)) (plus (cons u (vec A B)) (cons u (vec A B)))) pi); auto.
apply transitive with (plus (plus (plus (cons (vec A B) u) (cons u (vec A B))) (plus (cons (vec A B) u) (cons u (vec A B)))) pi); auto.
apply compatible; auto.
apply calcul4.
apply transitive with (plus (plus (cons (vec A B) (vec A B)) (cons (vec A B) (vec A B))) pi); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus zero zero) pi); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus (plus a a') (plus a a')) pi); auto.
apply compatible; auto.
apply compatible; auto.
apply transitive with (plus (plus (plus a a) (plus a' a')) pi); auto.
apply compatible; auto.
apply calcul4.
apply transitive with (plus (plus (double a) (plus a' a')) pi); auto.
apply transitive with (plus (double a) (plus (plus a' a') pi)); auto.
apply transitive with (plus (plus (plus a' a') pi) (double a)); auto.
apply compatible; auto.
apply transitive with (plus (plus a' a') (plus pisurdeux pisurdeux)); auto.
apply compatible; auto.
apply transitive with (plus (plus pisurdeux pisurdeux) (plus a' a')); auto.
apply calcul4.

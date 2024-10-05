Set Implicit Arguments.
Unset Strict Implicit.
Parameter V : Type.
Parameter AV : Type.
Parameter cons : V -> V -> AV.
Parameter R : AV -> AV -> Prop.
Axiom reflexive : forall a : AV, R a a.
Axiom symetrique : forall a b : AV, R a b -> R b a.
Axiom transitive : forall a b c : AV, R a b -> R b c -> R a c.
Parameter opp : V -> V.
Parameter zero : AV.
Parameter pi : AV.
Axiom angle_nul : forall u : V, R (cons u u) zero.
Axiom angle_plat : forall u : V, R (cons u (opp u)) pi.
Parameter plus : AV -> AV -> AV.
Axiom Chasles : forall u v w : V, R (plus (cons u v) (cons v w)) (cons u w).
Axiom non_vide_V : exists u : V, u = u.
Axiom angle_cons : forall (a : AV) (u : V), exists v : V, R a (cons u v).
Axiom compatible : forall a b c d : AV, R a b -> R c d -> R (plus a c) (plus b d).
Parameter vR : V -> V -> Prop.
Axiom v_refl : forall u : V, vR u u.
Axiom v_sym : forall u v : V, vR u v -> vR v u.
Axiom v_trans : forall u v w : V, vR u v -> vR v w -> vR u w.
Axiom opp_compatible : forall u v : V, vR u v -> vR (opp u) (opp v).
Axiom vR_R_compatible : forall u u' v v' : V, vR u u' -> vR v v' -> R (cons u v) (cons u' v').
Parameter PO : Type.
Parameter vec : PO -> PO -> V.
Axiom opp_vect : forall A B : PO, vR (opp (vec A B)) (vec B A).
Axiom non_vide_P : exists A : PO, A = A.
Axiom v_vec : forall (u : V) (A : PO), exists B : PO, vR u (vec A B).
Hint Resolve opp_opp opp_compatible v_refl v_sym.
Axiom plus_sym : forall a b : AV, R (plus a b) (plus b a).
Definition isocele (A B C : PO) : Prop := R (cons (vec B C) (vec B A)) (cons (vec C A) (vec C B)).
Definition double (a : AV) := plus a a.
Axiom calcul3 : forall a b c d e f : AV, R (plus (plus a (plus b c)) (plus d (plus e f))) (plus (plus a d) (plus (plus b e) (plus c f))).
Hint Resolve Chasles Chasles_2 angle_plat angle_nul oppu_u permute pi_plus_pi u_oppv oppu_oppv oppu_v point_angle.plus_assoc plus_zero zero_plus_a R_permute regulier plus_sym reflexive symetrique.
Hint Resolve double_zero.
Axiom calcul4 : forall a b c d : AV, R (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
Hint Resolve double_permute.
Hint Resolve R_double.
Hint Resolve double_plus.
Definition colineaire (u v : V) : Prop := R (double (cons u v)) zero.
Definition orthogonal (u v : V) := R (double (cons u v)) pi.
Hint Resolve orthogonal_sym.

Lemma permute : forall u v : V, R (plus (cons u v) (cons v u)) zero.
intros u v; try assumption.
apply (transitive (a:=plus (cons u v) (cons v u)) (b:=cons u u) (c:=zero)); auto.
exact (Chasles u v u).
Admitted.

Lemma oppu_u : forall u : V, R (cons (opp u) u) pi.
intros u; try assumption.
apply transitive with (cons (opp u) (opp (opp u))).
apply vR_R_compatible.
apply v_refl.
apply v_sym; apply opp_opp.
Admitted.

Lemma pi_plus_pi : R (plus pi pi) zero.
elim non_vide_V.
intros u H; try assumption.
apply transitive with (plus (cons u (opp u)) (cons (opp u) u)).
apply compatible.
apply symetrique; auto.
apply angle_plat.
apply symetrique; auto.
apply oppu_u.
apply transitive with (cons u u).
apply Chasles.
auto.
Admitted.

Lemma u_oppv : forall u v : V, R (cons u (opp v)) (plus (cons u v) pi).
intros u v; try assumption.
apply transitive with (plus (cons u v) (cons v (opp v))).
apply symetrique; auto.
apply Chasles.
apply compatible.
apply reflexive.
Admitted.

Lemma oppu_v : forall u v : V, R (cons (opp u) v) (plus pi (cons u v)).
intros u v; try assumption.
apply transitive with (plus (cons (opp u) u) (cons u v)).
apply symetrique; auto.
apply Chasles.
apply compatible.
apply oppu_u.
Admitted.

Lemma Chasles_2 : forall u v w t : V, R (cons u t) (plus (cons u v) (plus (cons v w) (cons w t))).
intros u v w t; try assumption.
apply transitive with (plus (cons u v) (cons v t)).
apply symetrique; auto.
apply Chasles.
apply compatible.
apply reflexive.
apply symetrique; auto.
Admitted.

Lemma plus_assoc : forall a b c : AV, R (plus a (plus b c)) (plus (plus a b) c).
intros a b c; try assumption.
elim non_vide_V; intros u H; clear H.
elim angle_cons with (a := a) (u := u); intros v H; try exact H.
elim angle_cons with (a := b) (u := v); intros v0 H0; try exact H0.
elim angle_cons with (a := c) (u := v0); intros v1 H1; try exact H1.
apply transitive with (plus (cons u v) (plus (cons v v0) (cons v0 v1))).
apply compatible; auto.
apply compatible; auto.
apply transitive with (cons u v1).
apply symetrique; auto.
apply Chasles_2.
apply transitive with (plus (cons u v0) (cons v0 v1)).
apply symetrique; auto.
apply Chasles.
apply compatible; auto.
apply transitive with (plus (cons u v) (cons v v0)).
apply symetrique; auto.
apply Chasles.
apply compatible; auto.
apply symetrique; auto.
apply symetrique; auto.
Admitted.

Lemma compatible_croix : forall a b c d : AV, R a b -> R c d -> R (plus a d) (plus b c).
intros a b c d H H0; try assumption.
apply compatible.
try exact H.
Admitted.

Lemma plus_zero : forall u v : V, R (plus (cons u v) zero) (cons u v).
intros u v; try assumption.
apply transitive with (plus (cons u v) (cons v v)).
apply compatible.
apply reflexive.
apply symetrique; auto.
apply angle_nul.
Admitted.

Lemma zero_plus : forall u v : V, R (plus zero (cons u v)) (cons u v).
intros u v; try assumption.
apply transitive with (plus (cons u u) (cons u v)).
apply compatible.
apply symetrique; auto.
apply angle_nul.
apply reflexive.
Admitted.

Lemma pi_plus_zero : R (plus pi zero) pi.
elim non_vide_V.
intros u H; try assumption.
apply transitive with (plus (cons u (opp u)) zero).
apply compatible.
apply symetrique.
apply angle_plat.
apply reflexive.
apply transitive with (cons u (opp u)).
apply plus_zero.
Admitted.

Lemma opp_opp : forall u : V, vR (opp (opp u)) u.
intros u; try assumption.
elim non_vide_P; intros A H; clear H.
elim v_vec with (u := u) (A := A); intros B H; try exact H.
apply v_trans with (opp (opp (vec A B))).
apply opp_compatible; apply opp_compatible.
try exact H.
apply v_trans with (opp (vec B A)).
apply opp_compatible.
apply v_trans with (vec B A).
apply opp_vect.
apply v_refl.
apply v_trans with (vec A B).
apply opp_vect.
apply v_sym; auto.

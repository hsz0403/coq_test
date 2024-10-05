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

Lemma regulier : forall a b c d : AV, R a c -> R (plus a b) (plus c d) -> R b d.
intros a b c d H H0; try assumption.
elim non_vide_V; intros u H1; clear H1.
elim angle_cons with (a := a) (u := u); intros v H1; try exact H1.
elim angle_cons with (a := c) (u := u); intros w H2; try exact H2.
elim angle_cons with (a := b) (u := v); intros t H3; try exact H3.
elim angle_cons with (a := d) (u := w); intros s H4; try exact H4.
cut (R (cons v t) (cons w s)); intros.
apply transitive with (cons v t).
try exact H3.
apply transitive with (cons w s).
try exact H5.
apply symetrique; auto.
apply regulier_cons with u.
apply transitive with a.
apply symetrique; auto.
apply transitive with c; auto.
apply transitive with (plus (cons u v) (cons v t)).
apply symetrique; auto.
apply Chasles.
apply transitive with (plus a b).
apply compatible.
apply symetrique; auto.
apply symetrique; auto.
apply transitive with (plus c d).
try exact H0.
apply transitive with (plus (cons u w) (cons w s)).
apply compatible.
try exact H2.
try exact H4.
apply Chasles.

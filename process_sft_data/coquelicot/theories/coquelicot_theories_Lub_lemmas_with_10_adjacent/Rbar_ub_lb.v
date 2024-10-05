Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Markov.
Open Scope R_scope.
Definition is_ub_Rbar (E : R -> Prop) (l : Rbar) := forall (x : R), E x -> Rbar_le x l.
Definition is_lb_Rbar (E : R -> Prop) (l : Rbar) := forall (x : R), E x -> Rbar_le l x.
Definition is_lub_Rbar (E : R -> Prop) (l : Rbar) := is_ub_Rbar E l /\ (forall b, is_ub_Rbar E b -> Rbar_le l b).
Definition is_glb_Rbar (E : R -> Prop) (l : Rbar) := is_lb_Rbar E l /\ (forall b, is_lb_Rbar E b -> Rbar_le b l).
Definition Lub_Rbar (E : R -> Prop) := proj1_sig (ex_lub_Rbar E).
Definition Glb_Rbar (E : R -> Prop) := proj1_sig (ex_glb_Rbar E).
Definition Rbar_is_upper_bound (E : Rbar -> Prop) (l : Rbar) := forall x, E x -> Rbar_le x l.
Definition Rbar_is_lower_bound (E : Rbar -> Prop) (l : Rbar) := forall x, E x -> Rbar_le l x.
Definition Rbar_is_lub (E : Rbar -> Prop) (l : Rbar) := Rbar_is_upper_bound E l /\ (forall b : Rbar, Rbar_is_upper_bound E b -> Rbar_le l b).
Definition Rbar_is_glb (E : Rbar -> Prop) (l : Rbar) := Rbar_is_lower_bound E l /\ (forall b : Rbar, Rbar_is_lower_bound E b -> Rbar_le b l).
Definition Rbar_lub (E : Rbar -> Prop) := proj1_sig (Rbar_ex_lub E).
Definition Rbar_glb (E : Rbar -> Prop) := proj1_sig (Rbar_ex_glb E).
Definition Empty (E : R -> Prop) := Lub_Rbar (fun x => x = 0 \/ E x) = Glb_Rbar (fun x => x = 0 \/ E x) /\ Lub_Rbar (fun x => x = 1 \/ E x) = Glb_Rbar (fun x => x = 1 \/ E x).

Lemma is_lub_Rbar_unique (E : R -> Prop) (l : Rbar) : is_lub_Rbar E l -> Lub_Rbar E = l.
Proof.
move => Hl ; rewrite /Lub_Rbar ; case: ex_lub_Rbar => l' /= Hl'.
apply Rbar_le_antisym.
by apply Hl', Hl.
Admitted.

Lemma is_glb_Rbar_unique (E : R -> Prop) (l : Rbar) : is_glb_Rbar E l -> Glb_Rbar E = l.
Proof.
move => Hl ; rewrite /Glb_Rbar ; case: ex_glb_Rbar => l' /= Hl'.
apply Rbar_le_antisym.
by apply Hl, Hl'.
Admitted.

Lemma Lub_Rbar_correct (E : R -> Prop) : is_lub_Rbar E (Lub_Rbar E).
Proof.
Admitted.

Lemma Glb_Rbar_correct (E : R -> Prop) : is_glb_Rbar E (Glb_Rbar E).
Proof.
Admitted.

Lemma is_lub_Rbar_subset (E1 E2 : R -> Prop) (l1 l2 : Rbar) : (forall x : R, E2 x -> E1 x) -> is_lub_Rbar E1 l1 -> is_lub_Rbar E2 l2 -> Rbar_le l2 l1.
Proof.
move => H [ub1 _] [_ lub2].
Admitted.

Lemma is_glb_Rbar_subset (E1 E2 : R -> Prop) (l1 l2 : Rbar) : (forall x : R, E2 x -> E1 x) -> is_glb_Rbar E1 l1 -> is_glb_Rbar E2 l2 -> Rbar_le l1 l2.
Proof.
move => H [ub1 _] [_ lub2].
Admitted.

Lemma is_lub_Rbar_eqset (E1 E2 : R -> Prop) (l : Rbar) : (forall x : R, E2 x <-> E1 x) -> is_lub_Rbar E1 l -> is_lub_Rbar E2 l.
Proof.
move => H [ub1 lub1] ; split.
apply (is_ub_Rbar_subset E1) ; [apply H | apply ub1].
Admitted.

Lemma is_glb_Rbar_eqset (E1 E2 : R -> Prop) (l : Rbar) : (forall x : R, E2 x <-> E1 x) -> is_glb_Rbar E1 l -> is_glb_Rbar E2 l.
Proof.
move => H [ub1 lub1] ; split.
apply (is_lb_Rbar_subset E1) ; [apply H | apply ub1].
Admitted.

Lemma Lub_Rbar_eqset (E1 E2 : R -> Prop) : (forall x, E1 x <-> E2 x) -> Lub_Rbar E1 = Lub_Rbar E2.
Proof.
move => H ; rewrite {2}/Lub_Rbar ; case: ex_lub_Rbar => l /= Hl.
apply is_lub_Rbar_unique.
Admitted.

Lemma Glb_Rbar_eqset (E1 E2 : R -> Prop) : (forall x, E1 x <-> E2 x) -> Glb_Rbar E1 = Glb_Rbar E2.
Proof.
move => H ; rewrite {2}/Glb_Rbar ; case: (ex_glb_Rbar E2) => l2 H2 /=.
apply is_glb_Rbar_unique.
Admitted.

Lemma Rbar_lb_ub (E : Rbar -> Prop) (l : Rbar) : Rbar_is_lower_bound (fun x => E (Rbar_opp x)) (Rbar_opp l) <-> Rbar_is_upper_bound E l.
Proof.
split => Hl x Hx.
apply Rbar_opp_le.
apply Hl.
by rewrite Rbar_opp_involutive.
apply Rbar_opp_le.
rewrite Rbar_opp_involutive.
Admitted.

Lemma is_ub_Rbar_correct (E : R -> Prop) (l : Rbar) : is_ub_Rbar E l <-> Rbar_is_upper_bound (fun x => is_finite x /\ E x) l.
Proof.
Admitted.

Lemma is_lb_Rbar_correct (E : R -> Prop) (l : Rbar) : is_lb_Rbar E l <-> Rbar_is_lower_bound (fun x => is_finite x /\ E x) l.
Proof.
Admitted.

Lemma Rbar_ub_p_infty (E : Rbar -> Prop) : Rbar_is_upper_bound E p_infty.
Proof.
Admitted.

Lemma Rbar_lb_m_infty (E : Rbar -> Prop) : Rbar_is_lower_bound E m_infty.
Proof.
Admitted.

Lemma Rbar_ub_Finite (E : Rbar -> Prop) (l : R) : Rbar_is_upper_bound E l -> is_upper_bound (fun (x : R) => E x) l.
Proof.
intros H x Ex.
Admitted.

Lemma Rbar_lb_Finite (E : Rbar -> Prop) (l : R) : Rbar_is_lower_bound E (Finite l) -> is_upper_bound (fun x => E (Finite (- x))) (- l).
Proof.
intros H x Ex.
Admitted.

Lemma Rbar_ub_m_infty (E : Rbar -> Prop) : Rbar_is_upper_bound E m_infty -> forall x, E x -> x = m_infty.
Proof.
Admitted.

Lemma Rbar_lb_p_infty (E : Rbar -> Prop) : Rbar_is_lower_bound E p_infty -> (forall x, E x -> x = p_infty).
Proof.
intros H x ; case x ; auto ; clear x ; [intros x| ] ; intros Hx.
case (H _ Hx) ; simpl ; intuition.
Admitted.

Lemma Rbar_lb_le_ub (E : Rbar -> Prop) (l1 l2 : Rbar) : (exists x, E x) -> Rbar_is_lower_bound E l1 -> Rbar_is_upper_bound E l2 -> Rbar_le l1 l2.
Proof.
Admitted.

Lemma Rbar_ub_lb (E : Rbar -> Prop) (l : Rbar) : Rbar_is_upper_bound (fun x => E (Rbar_opp x)) (Rbar_opp l) <-> Rbar_is_lower_bound E l.
Proof.
split => Hl x Hx.
apply Rbar_opp_le.
apply Hl.
by rewrite Rbar_opp_involutive.
apply Rbar_opp_le.
rewrite Rbar_opp_involutive.
by apply Hl.

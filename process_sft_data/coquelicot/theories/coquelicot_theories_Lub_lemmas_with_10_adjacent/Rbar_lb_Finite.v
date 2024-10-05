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

Lemma Rbar_ub_lb (E : Rbar -> Prop) (l : Rbar) : Rbar_is_upper_bound (fun x => E (Rbar_opp x)) (Rbar_opp l) <-> Rbar_is_lower_bound E l.
Proof.
split => Hl x Hx.
apply Rbar_opp_le.
apply Hl.
by rewrite Rbar_opp_involutive.
apply Rbar_opp_le.
rewrite Rbar_opp_involutive.
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

Lemma Rbar_lb_eq_ub (E : Rbar -> Prop) (l : Rbar) : Rbar_is_lower_bound E l -> Rbar_is_upper_bound E l -> forall x, E x -> x = l.
Proof.
intros Hl Hu x Hx.
Admitted.

Lemma Rbar_ub_dec (E : Rbar -> Prop) (Hp : ~ E p_infty) : {M : R | Rbar_is_upper_bound E M} + {(forall (M : R), ~Rbar_is_upper_bound E M)}.
Proof.
destruct (is_ub_Rbar_dec E) as [ [M HM] | HM ].
left ; exists M ; case => [x | | ] //= Hx.
by apply HM.
right => M.
specialize (HM M).
contradict HM => x Hx.
Admitted.

Lemma Rbar_lb_dec (E : Rbar -> Prop) (Hm : ~ E m_infty) : {M : R | Rbar_is_lower_bound E (Finite M)} + {(forall M, ~Rbar_is_lower_bound E (Finite M))}.
Proof.
destruct (Rbar_ub_dec (fun x => E (Rbar_opp x)) Hm) as [(M, H)|H].
left ; exists (-M).
apply Rbar_ub_lb ; simpl ; rewrite (Ropp_involutive M) ; auto.
Admitted.

Lemma Rbar_is_ub_subset (E1 E2 : Rbar -> Prop) (l : Rbar) : (forall x, E1 x -> E2 x) -> (Rbar_is_upper_bound E2 l) -> (Rbar_is_upper_bound E1 l).
Proof.
Admitted.

Lemma Rbar_is_lb_subset (E1 E2 : Rbar -> Prop) (l : Rbar) : (forall x, E1 x -> E2 x) -> (Rbar_is_lower_bound E2 l) -> (Rbar_is_lower_bound E1 l).
Proof.
Admitted.

Lemma Rbar_lub_glb (E : Rbar -> Prop) (l : Rbar) : Rbar_is_lub (fun x => E (Rbar_opp x)) (Rbar_opp l) <-> Rbar_is_glb E l.
Proof.
split ; [intros (ub, lub) | intros (lb, glb)] ; split.
apply Rbar_ub_lb ; auto.
intros b Hb ; generalize (lub _ (proj2 (Rbar_ub_lb _ _) Hb)) ; apply Rbar_opp_le.
apply Rbar_lb_ub ; intros x ; simpl ; repeat rewrite Rbar_opp_involutive ; apply lb.
intros b Hb.
Admitted.

Lemma Rbar_glb_lub (E : Rbar -> Prop) (l : Rbar) : Rbar_is_glb (fun x => E (Rbar_opp x)) (Rbar_opp l) <-> Rbar_is_lub E l.
Proof.
split ; [ intros (lb, glb) | intros (ub, lub)] ; split.
apply Rbar_lb_ub ; auto.
intros b Hb ; generalize (glb _ (proj2 (Rbar_lb_ub _ _) Hb)) ; apply Rbar_opp_le.
apply Rbar_ub_lb ; intro x ; simpl ; repeat rewrite Rbar_opp_involutive ; apply ub.
intros b Hb.
Admitted.

Lemma Rbar_lb_Finite (E : Rbar -> Prop) (l : R) : Rbar_is_lower_bound E (Finite l) -> is_upper_bound (fun x => E (Finite (- x))) (- l).
Proof.
intros H x Ex.
apply Ropp_le_cancel ; rewrite Ropp_involutive ; now apply (H (Finite (-x))).

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

Lemma is_ub_Rbar_opp (E : R -> Prop) (l : Rbar) : is_lb_Rbar E l <-> is_ub_Rbar (fun x => E (- x)) (Rbar_opp l).
Proof.
split ; intros Hl x Hx ; apply Rbar_opp_le.
now rewrite Rbar_opp_involutive ; apply Hl.
Admitted.

Lemma is_lb_Rbar_opp (E : R -> Prop) (l : Rbar) : is_ub_Rbar E l <-> is_lb_Rbar (fun x => E (- x)) (Rbar_opp l).
Proof.
split ; intros Hl x Hx ; apply Rbar_opp_le.
now rewrite Rbar_opp_involutive ; apply Hl.
Admitted.

Lemma is_ub_Rbar_dec (E : R -> Prop) : {l : R | is_ub_Rbar E l} + {(forall l : R, ~is_ub_Rbar E l)}.
Proof.
set (F (n : nat) (x : R) := x = 0 \/ (E x /\ x <= INR n)).
assert (F_b : forall n, bound (F n)).
intros ; exists (INR n) => x ; case => [-> | Hx].
by apply pos_INR.
by apply Hx.
assert (F_ex : forall n, (exists x : R, F n x)).
intros ; exists 0 ; by left.
set (u (n : nat) := proj1_sig (completeness (F n) (F_b n) (F_ex n))).
destruct (LPO_ub_dec u) as [ [M HM] | HM].
+
left ; exists M => x Hx.
destruct (nfloor_ex (Rmax 0 x)) as [n Hn].
by apply Rmax_l.
eapply Rle_trans, (HM (S n)).
rewrite /u ; case: completeness => l Hl /=.
apply Hl ; right ; split => //.
rewrite S_INR ; eapply Rle_trans, Rlt_le, Hn.
by apply Rmax_r.
+
right => l Hl.
case: (HM (Rmax 0 l)) => n {HM}.
apply Rle_not_lt.
rewrite /u ; case: completeness => M HM /=.
apply HM => x ; case => [ -> | Hx].
by apply Rmax_l.
eapply Rle_trans, Rmax_r.
Admitted.

Lemma is_lb_Rbar_dec (E : R -> Prop) : {l : R | is_lb_Rbar E l} + {(forall l : R, ~is_lb_Rbar E l)}.
Proof.
destruct (is_ub_Rbar_dec (fun x => E (- x))) as [ [l Hl] | Hl ].
left ; exists (Rbar_opp l).
by apply is_ub_Rbar_opp ; rewrite (Rbar_opp_involutive l).
right => l.
specialize (Hl (Rbar_opp l)).
contradict Hl.
Admitted.

Lemma is_ub_Rbar_subset (E1 E2 : R -> Prop) (l : Rbar) : (forall x : R, E2 x -> E1 x) -> is_ub_Rbar E1 l -> is_ub_Rbar E2 l.
Proof.
move => H ub1 x Hx.
Admitted.

Lemma is_lb_Rbar_subset (E1 E2 : R -> Prop) (l : Rbar) : (forall x : R, E2 x -> E1 x) -> is_lb_Rbar E1 l -> is_lb_Rbar E2 l.
Proof.
move => H ub1 x Hx.
Admitted.

Lemma is_lub_Rbar_opp (E : R -> Prop) (l : Rbar) : is_glb_Rbar E l <-> is_lub_Rbar (fun x => E (- x)) (Rbar_opp l).
Proof.
split => [[lb glb] | [ub lub] ] ; split.
by apply is_ub_Rbar_opp.
intros b Hb.
apply Rbar_opp_le ; rewrite Rbar_opp_involutive.
apply glb, is_ub_Rbar_opp ; by rewrite Rbar_opp_involutive.
by apply is_ub_Rbar_opp.
intros b Hb.
apply Rbar_opp_le.
Admitted.

Lemma is_glb_Rbar_opp (E : R -> Prop) (l : Rbar) : is_lub_Rbar E l <-> is_glb_Rbar (fun x => E (- x)) (Rbar_opp l).
Proof.
split => [[lb glb] | [ub lub] ] ; split.
by apply is_lb_Rbar_opp.
intros b Hb.
apply Rbar_opp_le ; rewrite Rbar_opp_involutive.
apply glb, is_lb_Rbar_opp ; by rewrite Rbar_opp_involutive.
by apply is_lb_Rbar_opp.
intros b Hb.
apply Rbar_opp_le.
Admitted.

Lemma ex_lub_Rbar (E : R -> Prop) : {l : Rbar | is_lub_Rbar E l}.
Proof.
destruct (is_ub_Rbar_dec E) as [[M HM] | HM] ; first last.
exists p_infty ; split.
by [].
case => [l | | ] // Hl.
by specialize (HM l).
specialize (HM 0).
contradict HM => x Hx.
by specialize (Hl x Hx).
rename E into F.
assert (F_b : bound F).
exists M => x Hx.
by apply HM.
clear -F_b.
set (E (m : nat) (x : R) := x = - INR m \/ F x).
assert (E_b : forall m, bound (E m)).
intros m.
case: F_b => l Hl.
exists (Rmax l (- INR m)) => x ; case => [ -> | Hx].
by apply Rmax_r.
eapply Rle_trans, Rmax_l.
by apply Hl.
assert (E_ex : forall m, exists x : R, E m x).
intros m ; exists (- INR m) ; by left.
set (u m := proj1_sig (completeness (E m) (E_b m) (E_ex m))).
destruct (LPO (fun n => u n <> - INR n)) as [ [n Hn] | Hn].
intros n.
case: (Req_EM_T (u n) (- INR n)) => H.
by right.
by left.
exists (u n).
move: Hn ; rewrite /u ; case: completeness => l Hl /= H.
split.
intros x Hx.
apply Hl ; by right.
assert (- INR n < l).
case: Hl => Hl _.
case: (Hl (-INR n)) => //=.
by left.
intros H0 ; contradict H.
by rewrite -H0.
case => [b | | ] //= Hb.
+
apply Hl => x Hx.
case: Hx => Hx ; first last.
by apply Hb.
rewrite Hx.
apply Rnot_lt_le ; contradict H0.
apply Rle_not_lt.
apply Hl => y Hy.
case: Hy => Hy.
rewrite Hy ; apply Rle_refl.
eapply Rle_trans, Rlt_le, H0.
by apply Hb.
+
contradict H.
apply Rle_antisym ; apply Hl.
intros x Hx.
case: Hx => [-> | Hx] //.
by apply Rle_refl.
by apply Hb in Hx.
by left.
assert (forall n, u n = - INR n).
intros n.
specialize (Hn n).
case: (Req_dec (u n) (- INR n)) => // H.
clear Hn.
exists m_infty ; split => // x Hx.
destruct (nfloor_ex (Rmax 0 (- x))) as [n Hn].
by apply Rmax_l.
specialize (H (S n)).
contradict H.
apply Rgt_not_eq.
rewrite /u S_INR ; case: completeness => l Hl /=.
eapply Rlt_le_trans with x.
apply Ropp_lt_cancel ; rewrite Ropp_involutive.
eapply Rle_lt_trans, Hn.
by apply Rmax_r.
apply Hl.
Admitted.

Lemma ex_glb_Rbar (E : R -> Prop) : {l : Rbar | is_glb_Rbar E l}.
Proof.
case: (ex_lub_Rbar (fun x => E (- x))) => l Hl.
exists (Rbar_opp l).
Admitted.

Lemma is_lub_Rbar_unique (E : R -> Prop) (l : Rbar) : is_lub_Rbar E l -> Lub_Rbar E = l.
Proof.
move => Hl ; rewrite /Lub_Rbar ; case: ex_lub_Rbar => l' /= Hl'.
apply Rbar_le_antisym.
by apply Hl', Hl.
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

Lemma Rbar_lb_eq_ub (E : Rbar -> Prop) (l : Rbar) : Rbar_is_lower_bound E l -> Rbar_is_upper_bound E l -> forall x, E x -> x = l.
Proof.
intros Hl Hu x Hx.
Admitted.

Lemma is_glb_Rbar_unique (E : R -> Prop) (l : Rbar) : is_glb_Rbar E l -> Glb_Rbar E = l.
Proof.
move => Hl ; rewrite /Glb_Rbar ; case: ex_glb_Rbar => l' /= Hl'.
apply Rbar_le_antisym.
by apply Hl, Hl'.
by apply Hl', Hl.

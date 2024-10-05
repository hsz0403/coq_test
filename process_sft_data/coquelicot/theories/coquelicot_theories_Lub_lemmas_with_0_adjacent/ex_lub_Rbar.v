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
by right.

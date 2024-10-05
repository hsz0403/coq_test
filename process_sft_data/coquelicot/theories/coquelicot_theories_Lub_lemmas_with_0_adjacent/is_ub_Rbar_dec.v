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
apply Hl, Hx.

Require Import RIneq Rcomplements Omega.
Open Scope R_scope.

Lemma LPO_ub_dec : forall (u : nat -> R), {M : R | forall n, u n <= M} + {forall M : R, exists n, M < u n}.
Proof.
intros u.
destruct (LPO (fun M => forall n, u n <= (INR M))) as [ [M MHM] | HM ].
intros M.
destruct (LPO (fun n => INR M < u n)) as [[n Hn] | Hn].
intros n.
destruct (Rlt_dec (INR M) (u n)) as [H|H].
now left.
now right.
right ; contradict Hn.
now apply Rle_not_lt.
left ; intro n.
now apply Rnot_lt_le.
left ; now exists (INR M).
right ; intros M.
destruct (nfloor_ex (Rbasic_fun.Rmax 0 M)) as [m Hm].
now apply Rbasic_fun.Rmax_l.
specialize (HM (S m)).
apply LPO_notforall.
intros n.
destruct (Rlt_dec M (u n)) as [H|H].
now left.
now right.
contradict HM ; intros n.
rewrite S_INR.
eapply Rle_trans, Rlt_le, Hm.
eapply Rle_trans, Rbasic_fun.Rmax_r.
now apply Rnot_lt_le.

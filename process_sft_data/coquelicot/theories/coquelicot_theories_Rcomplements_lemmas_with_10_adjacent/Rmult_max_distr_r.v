Ltac evar_last := match goal with | |- ?f ?x => let tx := type of x in let tx := eval simpl in tx in let tmp := fresh "tmp" in evar (tmp : tx) ; refine (@eq_ind tx tmp f _ x _) ; unfold tmp ; clear tmp end.
Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Module MyNat.
End MyNat.
Require Import Even Div2.
Require Import mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool.
Open Scope R_scope.
Definition floor x := proj1_sig (floor_ex x).
Definition floor1 x := proj1_sig (floor1_ex x).
Definition nfloor x pr := proj1_sig (nfloor_ex x pr).
Definition nfloor1 x pr := proj1_sig (nfloor1_ex x pr).
Fixpoint pow2 (n : nat) : nat := match n with | O => 1%nat | S n => (2 * pow2 n)%nat end.
Definition pos_div_2 (eps : posreal) := mkposreal _ (is_pos_div_2 eps).
Definition sign (x : R) := match total_order_T 0 x with | inleft (left _) => 1 | inleft (right _) => 0 | inright _ => -1 end.
Definition belast {T : Type} (s : seq T) := match s with | [::] => [::] | h :: s => belast h s end.

Lemma sum_f_u_Sk (u : nat -> R) (n m : nat) : (n <= m)%nat -> sum_f (S n) (S m) u = sum_f n m (fun k => u (S k)).
Proof.
move => H ; rewrite /sum_f.
simpl minus.
elim: (m - n)%nat => [ | k IH] //=.
rewrite IH ; repeat apply f_equal.
Admitted.

Lemma sum_f_u_add (u : nat -> R) (p n m : nat) : (n <= m)%nat -> sum_f (n + p)%nat (m + p)%nat u = sum_f n m (fun k => u (k + p)%nat).
Proof.
move => H ; rewrite /sum_f.
rewrite ?(plus_comm _ p) -minus_plus_simpl_l_reverse.
elim: (m - n)%nat => [ | k IH] //=.
by rewrite plus_comm.
rewrite IH ; repeat apply f_equal.
Admitted.

Lemma sum_f_Sn_m (u : nat -> R) (n m : nat) : (n < m)%nat -> sum_f (S n) m u = sum_f n m u - u n.
Proof.
move => H.
elim: m n H => [ | m IH] // n H.
by apply lt_n_O in H.
rewrite sum_f_u_Sk ; try by intuition.
rewrite sum_f_n_Sm ; try by intuition.
replace (sum_f n m u + u (S m) - u n) with ((sum_f n m u - u n) + u (S m)) by ring.
apply lt_n_Sm_le, le_lt_eq_dec in H.
case: H => [ H | -> {n} ] //.
rewrite -IH => //.
rewrite /sum_f ; simpl.
rewrite MyNat.sub_succ_r.
apply lt_minus_O_lt in H.
rewrite -{3}(MyNat.sub_add n m) ; try by intuition.
case: (m-n)%nat H => {IH} [ | k] //= H.
by apply lt_n_O in H.
apply (f_equal (fun y => y + _)).
elim: k {H} => [ | k IH] //.
rewrite /sum_f_R0 -/sum_f_R0 IH ; repeat apply f_equal ; intuition.
Admitted.

Lemma sum_f_R0_skip (u : nat -> R) (n : nat) : sum_f_R0 (fun k => u (n - k)%nat) n = sum_f_R0 u n.
Proof.
suff H : forall n m, (n < m)%nat -> sum_f n m (fun k => u ((m - k) + n)%nat) = sum_f n m u.
case: n => [ | n] //.
move: (H _ _ (lt_O_Sn n)) => {H} H.
rewrite /sum_f in H.
transitivity (sum_f_R0 (fun x : nat => u (S n - (x + 0) + 0)%nat) (S n - 0)).
replace (S n - 0)%nat with (S n) by auto.
elim: {2 4}(S n) => [ | m IH] //.
simpl ; by rewrite plus_0_r.
rewrite /sum_f_R0 -/sum_f_R0 -IH.
apply f_equal.
by rewrite ?plus_0_r.
rewrite H.
replace (S n - 0)%nat with (S n) by auto.
elim: (S n) => [ | m IH] //.
rewrite /sum_f_R0 -/sum_f_R0 -IH.
apply f_equal.
by rewrite plus_0_r.
move => {n} n m H.
elim: m u H => [ | m IH] u H //.
apply lt_n_Sm_le, le_lt_eq_dec in H ; case: H IH => [H IH | -> _ {n}] //.
rewrite sum_f_n_Sm ; try by intuition.
replace (sum_f n (S m) u) with (sum_f n (S m) u - u n + u n) by ring.
rewrite -sum_f_Sn_m ; try by intuition.
rewrite sum_f_u_Sk ; try by intuition.
rewrite -(IH (fun k => u (S k))) => {IH} ; try by intuition.
apply f_equal2.
rewrite /sum_f.
elim: {1 3 4}(m - n)%nat (le_refl (m-n)%nat) => [ | k IH] // Hk ; rewrite /sum_f_R0 -/sum_f_R0.
apply f_equal.
rewrite plus_0_l MyNat.sub_add ; intuition.
rewrite IH ; try by intuition.
by rewrite minus_diag plus_0_l.
rewrite /sum_f.
rewrite -minus_Sn_m ; try by intuition.
rewrite minus_diag.
rewrite /sum_f_R0 -/sum_f_R0.
replace (1+m)%nat with (S m) by ring.
Admitted.

Lemma sum_f_chasles (u : nat -> R) (n m k : nat) : (n < m)%nat -> (m < k)%nat -> sum_f (S n) k u = sum_f (S n) m u + sum_f (S m) k u.
Proof.
move => Hnm Hmk.
rewrite ?sum_f_rw //.
ring.
Admitted.

Lemma Rplus_max_distr_l : forall a b c, a + Rmax b c = Rmax (a + b) (a + c).
Proof.
intros a b c.
unfold Rmax.
case Rle_dec ; intros H ; case Rle_dec ; intros H' ; try easy.
elim H'.
apply Rplus_le_compat_l with (1 := H).
elim H.
Admitted.

Lemma Rplus_max_distr_r : forall a b c, Rmax b c + a = Rmax (b + a) (c + a).
Proof.
intros a b c.
rewrite <- 3!(Rplus_comm a).
Admitted.

Lemma Rplus_min_distr_l : forall a b c, a + Rmin b c = Rmin (a + b) (a + c).
Proof.
intros a b c.
unfold Rmin.
case Rle_dec ; intros H ; case Rle_dec ; intros H' ; try easy.
elim H'.
apply Rplus_le_compat_l with (1 := H).
elim H.
Admitted.

Lemma Rplus_min_distr_r : forall a b c, Rmin b c + a = Rmin (b + a) (c + a).
Proof.
intros a b c.
rewrite <- 3!(Rplus_comm a).
Admitted.

Lemma Rmult_max_distr_l : forall a b c, 0 <= a -> a * Rmax b c = Rmax (a * b) (a * c).
Proof.
intros a b c Ha.
destruct Ha as [Ha|Ha].
unfold Rmax.
case Rle_dec ; intros H.
apply (Rmult_le_compat_l _ _ _ (Rlt_le _ _ Ha)) in H.
case Rle_dec ; intuition.
apply Rnot_le_lt, (Rmult_lt_compat_l _ _ _ Ha), Rlt_not_le in H.
case Rle_dec ; intuition.
rewrite <- Ha ; clear a Ha.
repeat rewrite Rmult_0_l.
unfold Rmax ; assert (H := Rle_refl 0).
Admitted.

Lemma Rmult_min_distr_l : forall a b c, 0 <= a -> a * Rmin b c = Rmin (a * b) (a * c).
Proof.
intros a b c Ha.
destruct Ha as [Ha|Ha].
unfold Rmin.
case Rle_dec ; intros H.
apply (Rmult_le_compat_l _ _ _ (Rlt_le _ _ Ha)) in H.
case Rle_dec ; intuition.
apply Rnot_le_lt, (Rmult_lt_compat_l _ _ _ Ha), Rlt_not_le in H.
case Rle_dec ; intuition.
rewrite <- Ha ; clear a Ha.
repeat rewrite Rmult_0_l.
unfold Rmin ; assert (H := Rle_refl 0).
Admitted.

Lemma Rmult_min_distr_r : forall a b c, 0 <= a -> Rmin b c * a = Rmin (b * a) (c * a).
Proof.
intros a b c.
rewrite <- 3!(Rmult_comm a).
Admitted.

Lemma Rmin_assoc : forall x y z, Rmin x (Rmin y z) = Rmin (Rmin x y) z.
intros x y z; unfold Rmin.
destruct (Rle_dec y z); destruct (Rle_dec x y); destruct (Rle_dec x z); destruct (Rle_dec y z) ; try intuition.
contradict n.
apply Rle_trans with y ; auto.
contradict r.
Admitted.

Lemma Rmax_assoc : forall x y z, Rmax x (Rmax y z) = Rmax (Rmax x y) z.
intros x y z; unfold Rmax.
destruct (Rle_dec y z); destruct (Rle_dec x y); destruct (Rle_dec x z); destruct (Rle_dec y z) ; try intuition.
contradict n.
apply Rle_trans with y ; auto.
contradict r.
Admitted.

Lemma Rmax_le_compat : forall a b c d, a <= b -> c <= d -> Rmax a c <= Rmax b d.
Proof.
intros.
unfold Rmax.
destruct (Rle_dec a c).
destruct (Rle_dec b d).
apply H0.
apply Rnot_le_lt in n.
apply (Rle_trans _ d).
apply H0.
apply (Rlt_le _ _ n).
destruct (Rle_dec b d).
apply (Rle_trans _ b).
apply H.
apply r.
Admitted.

Lemma Rmax_opp_Rmin : forall a b, Rmax (-a) (-b) = - Rmin a b.
Proof.
intros.
destruct (Rle_or_lt a b).
rewrite Rmax_left.
rewrite Rmin_left.
reflexivity.
apply H.
apply Ropp_le_contravar.
apply H.
rewrite Rmax_right.
rewrite Rmin_right.
reflexivity.
apply Rlt_le, H.
apply Ropp_le_contravar.
apply Rlt_le.
Admitted.

Lemma Rmin_opp_Rmax : forall a b, Rmin (-a) (-b) = - Rmax a b.
Proof.
intros.
rewrite Rmax_comm.
unfold Rmin ; case Rle_dec ; intro Hab.
apply Ropp_le_cancel in Hab.
unfold Rmax ; case Rle_dec ; intuition.
apply Rnot_le_lt, Ropp_lt_cancel, Rlt_not_le in Hab.
Admitted.

Lemma Rmax_mult : forall a b c, 0 <= c -> Rmax a b * c = Rmax (a * c) (b * c).
Proof.
intros.
repeat rewrite (Rmult_comm _ c).
apply sym_eq.
apply RmaxRmult.
Admitted.

Lemma Rmax_le_Rplus : forall a b : R, 0 <= a -> 0 <= b -> Rmax a b <= a + b.
Proof.
intros.
destruct (Rle_lt_dec a b).
rewrite <- (Rplus_0_l (Rmax a b)).
rewrite Rmax_right.
apply Rplus_le_compat_r.
apply H.
apply r.
rewrite <- (Rplus_0_r (Rmax a b)).
rewrite Rmax_left.
apply Rplus_le_compat_l.
apply H0.
Admitted.

Lemma Rplus_le_Rmax : forall a b : R, a + b <= 2*Rmax a b.
Proof.
intros.
rewrite RIneq.double.
destruct (Rle_lt_dec a b).
rewrite Rmax_right.
apply Rplus_le_compat_r.
apply r.
apply r.
rewrite Rmax_left.
apply Rplus_le_compat_l.
apply Rlt_le.
apply r.
Admitted.

Lemma Rmult_max_distr_r : forall a b c, 0 <= a -> Rmax b c * a = Rmax (b * a) (c * a).
Proof.
intros a b c.
rewrite <- 3!(Rmult_comm a).
apply Rmult_max_distr_l.

Require Import Reals mathcomp.ssreflect.ssreflect Psatz Omega.
Require Import Hierarchy PSeries Rbar Lim_seq.
Open Scope R_scope.
Fixpoint v (n : nat) : R := match n with | O => 7 / 10 * 250000 | S n => 95 / 100 * v n + 1 / 100 * c n end with c (n : nat) : R := match n with | O => 3 / 10 * 250000 | S n => 5 / 100 * v n + 99 / 100 * c n end.
Definition A : matrix 2 2 := [[95/100, 1/100 ] , [ 5/100, 99/100]].
Definition X (n : nat) : matrix 2 1 := [[v n],[c n]].
Lemma Q2 : forall n, X (S n) = scal A (X n).
Proof.
intros n.
rewrite /scal /= /Mmult.
apply (coeff_mat_ext 0).
case ; [ | case => //].
case ; [ | case => //] ; rewrite coeff_mat_bij /= ; (try omega) ; rewrite sum_Sn sum_O /plus /mult //=.
case ; [ | case => //] ; rewrite coeff_mat_bij /= ; (try omega) ; rewrite sum_Sn sum_O /plus /mult //=.
Qed.
Definition P : matrix 2 2 := [[1,-1], [5,1]].
Definition Q : matrix 2 2 := [[1,1],[-5,1]].
Goal mult P Q = [[6,0],[0,6]].
apply (coeff_mat_ext_aux 0 0) => i j Hi Hj.
rewrite coeff_mat_bij => //.
rewrite /coeff_mat /= /mult /plus /=.
(destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /= ; try ring) ; (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /= ; try ring) ; rewrite sum_Sn sum_O /= /plus /= ; ring.
Qed.
Goal mult Q P = [[6,0],[0,6]].
apply (coeff_mat_ext_aux 0 0) => i j Hi Hj.
rewrite coeff_mat_bij => //.
rewrite /coeff_mat /= /mult /plus /=.
(destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /= ; try ring) ; (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /= ; try ring) ; rewrite sum_Sn sum_O /= /plus /= ; ring.
Qed.
Definition P' : matrix 2 2 := [[1 / 6,1 / 6],[-5 / 6,1 / 6]].
Lemma Q3a : mult P P' = Mone /\ mult P' P = Mone.
Proof.
split.
apply (coeff_mat_ext_aux 0 0) => i j Hi Hj.
rewrite coeff_mat_bij => //.
rewrite /coeff_mat /= /mult /plus /=.
(destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /= ; try field) ; (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /one /= ; try field) ; rewrite sum_Sn sum_O /= /plus /= ; field.
apply (coeff_mat_ext_aux 0 0) => i j Hi Hj.
rewrite coeff_mat_bij => //.
rewrite /coeff_mat /= /mult /plus /=.
(destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /= ; try field) ; (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /one /= ; try field) ; rewrite sum_Sn sum_O /= /plus /= ; field.
Qed.
Definition D : matrix 2 2 := [[1,0],[0,94 / 100]].
Lemma Q3b : mult P' (mult A P) = D.
Proof.
apply (coeff_mat_ext_aux 0 0) => i j Hi Hj.
rewrite coeff_mat_bij => //.
rewrite /coeff_mat /= /mult /plus /=.
(destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /= ; try field) ; (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /one /= ; try field) ; rewrite sum_Sn sum_O /= /plus /= ; (try field) ; rewrite !sum_Sn !sum_O /= /plus /coeff_mat /= ; field.
Qed.
Lemma Q3c : forall n, pow_n A n = mult P (mult (pow_n D n) P').
Proof.
elim => /= [ | n IH].
rewrite mult_one_l.
apply sym_eq, Q3a.
by rewrite -{1}Q3b !mult_assoc (proj1 Q3a) mult_one_l -!mult_assoc IH.
Qed.
Lemma Q4 : forall n, v n = 1 / 6 * (1 + 5 * (94 / 100) ^ n) * v 0 + 1 / 6 * (1 - (94 / 100) ^ n) * c 0.
Proof.
intros n.
assert (X n = scal (pow_n A n) (X 0)).
elim: n => [ | n IH] /=.
by rewrite scal_one.
rewrite -scal_assoc -IH.
by apply Q2.
assert (pow_n D n = [[1,0], [0,(94 / 100)^n]]).
elim: (n) => [ | m IH] //=.
rewrite IH.
apply (coeff_mat_ext_aux 0 0) => i j Hi Hj.
rewrite coeff_mat_bij => //=.
rewrite /plus /mult /= /coeff_mat /=.
(destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /one /=) ; (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /one /= ; try field) ; rewrite sum_Sn sum_O /= /plus /= ; field.
rewrite Q3c H0 in H.
apply (proj1 (coeff_mat_ext 0 _ _)) with (i := O) (j := O) in H.
rewrite {1}/coeff_mat /= in H.
rewrite H ; repeat (rewrite !/coeff_mat /=).
rewrite !sum_Sn !sum_O /= /plus /mult /= ; field.
Qed.
Lemma lim_v : is_lim_seq v (41666 + 2 / 3).
Proof.
eapply is_lim_seq_ext.
intros n ; apply sym_eq, Q4.
eapply is_lim_seq_plus.
eapply is_lim_seq_mult.
eapply is_lim_seq_mult.
apply is_lim_seq_const.
eapply is_lim_seq_plus.
apply is_lim_seq_const.
eapply is_lim_seq_mult.
apply is_lim_seq_const.
apply is_lim_seq_geom.
rewrite Rabs_pos_eq ; lra.
by [].
by [].
by [].
apply is_lim_seq_const.
by [].
eapply is_lim_seq_mult.
eapply is_lim_seq_mult.
apply is_lim_seq_const.
eapply is_lim_seq_minus.
apply is_lim_seq_const.
apply is_lim_seq_geom.
rewrite Rabs_pos_eq ; lra.
by [].
by [].
apply is_lim_seq_const.
by [].
apply (f_equal (fun x => Some (Finite x))) ; simpl ; field.
Qed.
Lemma lim_c : is_lim_seq c (208333 + 1 / 3).
Proof.
assert (forall n, c n = 250000 - v n).
elim => [ | n /= ->] /= ; field.
eapply is_lim_seq_ext.
intros n ; apply sym_eq, H.
eapply is_lim_seq_minus.
apply is_lim_seq_const.
by apply lim_v.
apply (f_equal (fun x => Some (Finite x))) ; simpl ; field.
Qed.
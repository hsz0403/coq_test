Require Import Reals mathcomp.ssreflect.ssreflect Psatz Omega.
Require Import Hierarchy PSeries Rbar Lim_seq.
Open Scope R_scope.
Fixpoint v (n : nat) : R := match n with | O => 7 / 10 * 250000 | S n => 95 / 100 * v n + 1 / 100 * c n end with c (n : nat) : R := match n with | O => 3 / 10 * 250000 | S n => 5 / 100 * v n + 99 / 100 * c n end.
Definition A : matrix 2 2 := [[95/100, 1/100 ] , [ 5/100, 99/100]].
Definition X (n : nat) : matrix 2 1 := [[v n],[c n]].
Definition P : matrix 2 2 := [[1,-1], [5,1]].
Definition Q : matrix 2 2 := [[1,1],[-5,1]].
Goal mult P Q = [[6,0],[0,6]].
apply (coeff_mat_ext_aux 0 0) => i j Hi Hj.
rewrite coeff_mat_bij => //.
rewrite /coeff_mat /= /mult /plus /=.
(destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /= ; try ring) ; (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /= ; try ring) ; rewrite sum_Sn sum_O /= /plus /= ; ring.
Goal mult Q P = [[6,0],[0,6]].
apply (coeff_mat_ext_aux 0 0) => i j Hi Hj.
rewrite coeff_mat_bij => //.
rewrite /coeff_mat /= /mult /plus /=.
(destruct i as [ | i] ; destruct j as [ | j] ; rewrite /zero /= ; try ring) ; (try (destruct i as [ | i]) ; try (destruct j as [ | j]) ; rewrite /zero /= ; try ring) ; rewrite sum_Sn sum_O /= /plus /= ; ring.
Definition P' : matrix 2 2 := [[1 / 6,1 / 6],[-5 / 6,1 / 6]].
Definition D : matrix 2 2 := [[1,0],[0,94 / 100]].

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

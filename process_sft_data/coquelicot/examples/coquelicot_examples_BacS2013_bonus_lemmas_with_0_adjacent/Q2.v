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

Lemma Q2 : forall n, X (S n) = scal A (X n).
Proof.
intros n.
rewrite /scal /= /Mmult.
apply (coeff_mat_ext 0).
case ; [ | case => //].
case ; [ | case => //] ; rewrite coeff_mat_bij /= ; (try omega) ; rewrite sum_Sn sum_O /plus /mult //=.
case ; [ | case => //] ; rewrite coeff_mat_bij /= ; (try omega) ; rewrite sum_Sn sum_O /plus /mult //=.

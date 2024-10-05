Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect Rbar.
Require Import Rcomplements.
Require Import Lim_seq Continuity Derive Series.
Require Import Lub Hierarchy.
Open Scope R_scope.
Definition CVS_dom (fn : nat -> R -> R) (D : R -> Prop) := forall x : R, D x -> ex_finite_lim_seq (fun n => fn n x).
Definition CVU_dom (fn : nat -> R -> R) (D : R -> Prop) := forall eps : posreal, eventually (fun n => forall x : R, D x -> Rabs ((fn n x) - real (Lim_seq (fun n => fn n x))) < eps).
Definition CVU_cauchy (fn : nat -> R -> R) (D : R -> Prop) := forall eps : posreal, exists N : nat, forall (n m : nat) (x : R), D x -> (N <= n)%nat -> (N <= m)%nat -> Rabs (fn n x - fn m x) < eps.
Definition is_connected (D : R -> Prop) := forall a b x, D a -> D b -> a <= x <= b -> D x.

Lemma CVN_CVU_r (fn : nat -> R -> R) (r : posreal) : CVN_r fn r -> forall x, (Rabs x < r) -> exists e : posreal, CVU (fun n => SP fn n) (fun x => Series (fun n => fn n x)) x e.
Proof.
case => An [l [H H0]] x Hx.
assert (H1 : ex_series An).
apply ex_series_Reals_1.
exists l => e He.
case: (H e He) => {H} N H.
exists N => n Hn.
replace (sum_f_R0 An n) with (sum_f_R0 (fun k : nat => Rabs (An k)) n).
by apply H.
elim: n {Hn} => /= [ | n IH].
apply Rabs_pos_eq.
apply Rle_trans with (Rabs (fn O 0)).
by apply Rabs_pos.
apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
rewrite IH Rabs_pos_eq.
by [].
apply Rle_trans with (Rabs (fn (S n) 0)).
by apply Rabs_pos.
apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
have H2 : is_lim_seq (fun n => Series (fun k => An (n + k)%nat)) 0.
apply is_lim_seq_incr_1.
apply is_lim_seq_ext with (fun n => Series An - sum_f_R0 An n).
move => n ; rewrite (Series_incr_n An (S n)) /=.
ring.
by apply lt_O_Sn.
by apply H1.
replace (Finite 0) with (Rbar_plus (Series An) (- Series An)) by (simpl ; apply Rbar_finite_eq ; ring).
apply (is_lim_seq_plus _ _ (Series An) (-Series An)).
by apply is_lim_seq_const.
replace (Finite (-Series An)) with (Rbar_opp (Series An)) by (simpl ; apply Rbar_finite_eq ; ring).
apply -> is_lim_seq_opp.
rewrite /Series ; apply (is_lim_seq_ext (sum_n (fun k => An k))).
elim => /= [ | n IH].
by rewrite sum_O.
by rewrite sum_Sn IH.
apply is_lim_seq_ext with (sum_n An).
move => n ; by rewrite sum_n_Reals.
apply Lim_seq_correct', H1.
easy.
assert (H3 : forall y, Boule 0 r y -> ex_series (fun n => Rabs (fn n y))).
move => y Hy.
move: H1 ; apply @ex_series_le.
move => n.
rewrite /norm /= /abs /= Rabs_Rabsolu.
by apply H0.
apply Rminus_lt_0 in Hx.
set r0 := mkposreal _ Hx.
exists r0 => e He ; set eps := mkposreal e He.
apply is_lim_seq_spec in H2.
case: (H2 eps) => {H2} N H2.
exists N => n y Hn Hy.
have H4 : Boule 0 r y.
rewrite /Boule /= in Hy |- *.
apply Rle_lt_trans with (1 := Rabs_triang_inv _ _) in Hy.
rewrite /Rminus ?(Rplus_comm _ (-Rabs x)) in Hy.
apply Rplus_lt_reg_l in Hy.
by rewrite Rminus_0_r.
apply Rle_lt_trans with (2 := H2 (S n) (le_trans _ _ _ (le_n_Sn _) (le_n_S _ _ Hn))).
rewrite Rminus_0_r /SP.
rewrite (Series_incr_n (fun k : nat => fn k y) (S n)) /=.
ring_simplify (sum_f_R0 (fun k : nat => fn k y) n + Series (fun k : nat => fn (S (n + k)) y) - sum_f_R0 (fun k : nat => fn k y) n).
apply Rle_trans with (2 := Rle_abs _).
apply Rle_trans with (Series (fun k : nat => Rabs (fn (S (n + k)) y))).
apply Series_Rabs.
apply ex_series_ext with (fun n0 : nat => Rabs (fn (S (n) + n0)%nat y)).
move => n0 ; by rewrite plus_Sn_m.
apply (ex_series_incr_n (fun n => Rabs (fn n y))).
by apply H3.
apply Series_le.
move => k ; split.
by apply Rabs_pos.
by apply H0.
apply ex_series_ext with (fun k : nat => An (S n + k)%nat).
move => k ; by rewrite plus_Sn_m.
by apply ex_series_incr_n.
by apply lt_O_Sn.
apply ex_series_Rabs.
by apply H3.

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

Lemma CVU_dom_cauchy (fn : nat -> R -> R) (D : R -> Prop) : CVU_dom fn D <-> CVU_cauchy fn D.
Proof.
split => H eps.
case: (H (pos_div_2 eps)) => {H} N /= H.
exists N => n m x Hx Hn Hm.
rewrite (double_var eps).
replace (fn n x - fn m x) with ((fn n x - real (Lim_seq (fun n0 : nat => fn n0 x))) - (fn m x - real (Lim_seq (fun n0 : nat => fn n0 x)))) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _) ; rewrite Rabs_Ropp.
apply Rplus_lt_compat ; by apply H.
rewrite /Lim_seq.
case: (H (pos_div_2 eps)) => {H} N /= H.
exists N => n Hn x Hx.
rewrite /LimSup_seq ; case: ex_LimSup_seq ; case => [ls | | ] /= Hls.
rewrite /LimInf_seq ; case: ex_LimInf_seq ; case => [li | | ] /= Hli.
replace (fn n x - (ls + li) / 2) with (((fn n x - ls) + (fn n x - li))/2) by field.
rewrite Rabs_div ; [ | by apply Rgt_not_eq, Rlt_R0_R2].
rewrite (Rabs_pos_eq 2) ; [ | by apply Rlt_le, Rlt_R0_R2].
rewrite Rlt_div_l ; [ | by apply Rlt_R0_R2].
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (eps * 2) with (eps + eps) by ring.
apply Rplus_lt_compat ; apply Rabs_lt_between'.
case: (Hls (pos_div_2 eps)) => {Hls Hli} /= H0 [N0 H1] ; split.
case: (H0 N) => {H0} m [Hm H0].
apply Rlt_trans with (fn m x - eps/2).
replace (ls - eps) with ((ls - eps / 2) - eps/2) by field.
by apply Rplus_lt_compat_r.
replace (fn n x) with (eps/2 + (fn n x - eps/2)) by ring.
replace (fn m x - eps / 2) with ((fn m x - fn n x) + (fn n x - eps/2)) by ring.
apply Rplus_lt_compat_r.
apply Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
apply Rlt_trans with (fn (n+N0)%nat x + eps/2).
replace (fn n x) with (fn (n + N0)%nat x + (fn n x - fn (n+N0)%nat x)) by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (1 := Rle_abs _).
apply H ; by intuition.
replace (ls + eps) with ((ls + eps/2) + eps/2) by field.
apply Rplus_lt_compat_r.
apply H1 ; by intuition.
case: (Hli (pos_div_2 eps)) => {Hls Hli} /= H0 [N0 H1] ; split.
apply Rlt_trans with (fn (n+N0)%nat x - eps/2).
replace (li - eps) with ((li - eps/2) - eps/2) by field.
apply Rplus_lt_compat_r.
apply H1 ; by intuition.
replace (fn n x) with (eps/2 + (fn n x - eps/2)) by ring.
replace (fn (n + N0)%nat x - eps / 2) with ((fn (n + N0)%nat x - fn n x) + (fn n x - eps/2)) by ring.
apply Rplus_lt_compat_r.
apply Rle_lt_trans with (1 := Rle_abs _).
apply H ; by intuition.
case: (H0 N) => {H0} m [Hm H0].
apply Rlt_trans with (fn m x + eps/2).
replace (fn n x) with (fn m x + (fn n x - fn m x)) by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
replace (li + eps) with ((li + eps / 2) + eps/2) by field.
by apply Rplus_lt_compat_r.
case: (Hli (fn n x + eps / 2)) => {Hls Hli} N0 H0.
move: (H0 _ (le_plus_r N N0)) => {H0} H0 ; contradict H0.
apply Rle_not_lt, Rlt_le.
replace (fn (N + N0)%nat x) with (fn n x + (fn (N + N0)%nat x - fn n x)) by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (1 := Rle_abs _).
apply H ; by intuition.
case: (Hli (fn n x - eps / 2) N) => {Hls Hli} m [Hm H0].
contradict H0.
apply Rle_not_lt, Rlt_le.
replace (fn m x) with (eps/2 + (fn m x - eps/2)) by ring.
replace (fn n x - eps / 2) with ((fn n x - fn m x) + (fn m x - eps/2)) by ring.
apply Rplus_lt_compat_r, Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
case: (Hls (fn n x + eps / 2) N) => {Hls} m [Hm H0].
contradict H0.
apply Rle_not_lt, Rlt_le.
replace (fn m x) with (fn n x + (fn m x - fn n x)) by ring.
apply Rplus_lt_compat_l, Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
case: (Hls (fn n x - eps / 2)) => {Hls} N0 H0.
move: (H0 _ (le_plus_r N N0)) => {H0} H0 ; contradict H0.
apply Rle_not_lt, Rlt_le.
replace (fn (N + N0)%nat x) with (eps/2 + (fn (N + N0)%nat x - eps/2)) by ring.
replace (fn n x - eps / 2) with ((fn n x - fn (N+N0)%nat x) + (fn (N+N0)%nat x - eps/2)) by ring.
apply Rplus_lt_compat_r.
apply Rle_lt_trans with (1 := Rle_abs _).
apply H ; by intuition.

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

Lemma CVU_limits_open (fn : nat -> R -> R) (D : R -> Prop) : open D -> CVU_dom fn D -> (forall x n, D x -> ex_finite_lim (fn n) x) -> forall x, D x -> ex_finite_lim_seq (fun n => real (Lim (fn n) x)) /\ ex_finite_lim (fun y => real (Lim_seq (fun n => fn n y))) x /\ real (Lim_seq (fun n => real (Lim (fn n) x))) = real (Lim (fun y => real (Lim_seq (fun n => fn n y))) x).
Proof.
move => Ho Hfn Hex x Hx.
have H : ex_finite_lim_seq (fun n : nat => real (Lim (fn n) x)).
apply CVU_dom_cauchy in Hfn.
apply ex_lim_seq_cauchy_corr => eps.
case: (Hfn (pos_div_2 eps)) => {Hfn} /= N Hfn.
exists N => n m Hn Hm.
case: (Hex x n Hx) => ln Hex_n ; rewrite (is_lim_unique _ _ _ Hex_n).
case: (Hex x m Hx) => {Hex} lm Hex_m ; rewrite (is_lim_unique _ _ _ Hex_m).
apply is_lim_spec in Hex_n.
apply is_lim_spec in Hex_m.
case: (Hex_n (pos_div_2 (pos_div_2 eps))) => {Hex_n} /= dn Hex_n.
case: (Hex_m (pos_div_2 (pos_div_2 eps))) => {Hex_m} /= dm Hex_m.
case: (Ho x Hx) => {Ho} d0 Ho.
set y := x + Rmin (Rmin dn dm) d0 / 2.
have Hd : 0 < Rmin (Rmin dn dm) d0 / 2.
apply Rdiv_lt_0_compat.
apply Rmin_case ; [ | by apply d0].
apply Rmin_case ; [ by apply dn | by apply dm].
exact: Rlt_R0_R2.
have Hy : Rabs (y - x) < d0.
rewrite /y ; ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hd)).
generalize (Rmin_r (Rmin dn dm) d0).
lra.
move : (Ho y Hy) => {Ho Hy} Hy.
replace (ln - lm) with (- (fn n y - ln) + (fn m y - lm) + (fn n y - fn m y)) by ring.
rewrite (double_var eps) ; apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
rewrite (double_var (eps/2)) ; apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
rewrite Rabs_Ropp ; apply Hex_n.
rewrite /y /ball /= /AbsRing_ball /= /minus /plus /opp /abs /=.
ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) + - x).
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hd)).
generalize (Rmin_l (Rmin dn dm) d0) (Rmin_l dn dm).
lra.
apply Rgt_not_eq, Rlt_gt, Rminus_lt_0.
rewrite /y ; by ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
apply Hex_m.
rewrite /y /ball /= /AbsRing_ball /= /minus /plus /opp /abs /=.
ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) + - x).
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hd)).
generalize (Rmin_l (Rmin dn dm) d0) (Rmin_r dn dm).
lra.
apply Rgt_not_eq, Rlt_gt, Rminus_lt_0.
rewrite /y ; by ring_simplify ((x + Rmin (Rmin dn dm) d0 / 2) - x).
by apply Hfn.
split.
exact: H.
apply Lim_seq_correct' in H.
move: (real (Lim_seq (fun n : nat => real (Lim (fn n) x)))) H => l H.
have H0 : is_lim (fun y : R => real (Lim_seq (fun n : nat => fn n y))) x l.
apply is_lim_spec.
move => eps.
apply is_lim_seq_spec in H.
case: (Hfn (pos_div_2 (pos_div_2 eps))) => {Hfn} /= n1 Hfn.
case: (H (pos_div_2 (pos_div_2 eps))) => {H} /= n2 H.
set n := (n1 + n2)%nat.
move: (fun y Hy => Hfn n (le_plus_l _ _) y Hy) => {Hfn} Hfn.
move: (H n (le_plus_r _ _)) => {H} H.
move: (Hex x n Hx) => {Hex} Hex.
apply Lim_correct' in Hex.
apply is_lim_spec in Hex.
case: (Hex (pos_div_2 eps)) => {Hex} /= d1 Hex.
case: (Ho x Hx) => {Ho} /= d0 Ho.
have Hd : 0 < Rmin d0 d1.
apply Rmin_case ; [by apply d0 | by apply d1].
exists (mkposreal _ Hd) => /= y Hy Hxy.
replace (real (Lim_seq (fun n0 : nat => fn n0 y)) - l) with ((real (Lim (fn n) x) - l) - (fn n y - real (Lim_seq (fun n : nat => fn n y))) + (fn n y - real (Lim (fn n) x))) by ring.
rewrite (double_var eps) ; apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
rewrite (double_var (eps/2)) ; apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
exact: H.
rewrite Rabs_Ropp ; apply Hfn.
by apply Ho, Rlt_le_trans with (1 := Hy), Rmin_l.
apply Hex.
by apply Rlt_le_trans with (1 := Hy), Rmin_r.
exact: Hxy.
split.
by exists l.
replace l with (real l) by auto.
by apply sym_eq, (f_equal real), is_lim_unique.

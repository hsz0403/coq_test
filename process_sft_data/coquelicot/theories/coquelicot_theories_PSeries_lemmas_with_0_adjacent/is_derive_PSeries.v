Require Import Reals Even Div2 Omega Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Lim_seq Lub Hierarchy.
Require Import Continuity Derive Seq_fct Series.
Section Definitions.
Context {K : AbsRing} {V : NormedModule K}.
Definition is_pseries (a : nat -> V) (x:K) (l : V) := is_series (fun k => scal (pow_n x k) (a k)) l.
Definition ex_pseries (a : nat -> V) (x : K) := ex_series (fun k => scal (pow_n x k) (a k)).
End Definitions.
Definition PSeries (a : nat -> R) (x : R) : R := Series (fun k => a k * x ^ k).
Section Extensionality.
Context {K : AbsRing} {V : NormedModule K}.
End Extensionality.
Section ConvergenceCircle.
Context {K : AbsRing} {V : NormedModule K}.
End ConvergenceCircle.
Definition CV_disk (a : nat -> R) (r : R) := ex_series (fun n => Rabs (a n * r^n)).
Definition CV_radius (a : nat -> R) : Rbar := Lub_Rbar (CV_disk a).
Section PS_plus.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_plus (a b : nat -> V) (n : nat) : V := plus (a n) (b n).
End PS_plus.
Section PS_scal.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_scal (c : K) (a : nat -> V) (n : nat) : V := scal c (a n).
End PS_scal.
Definition PS_scal_r (c : R) (a : nat -> R) (n : nat) : R := a n * c.
Section PS_incr.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_incr_1 (a : nat -> V) (n : nat) : V := match n with | 0 => zero | S n => a n end.
Fixpoint PS_incr_n (a : nat -> V) (n k : nat) : V := match n with | O => a k | S n => PS_incr_1 (PS_incr_n a n) k end.
Definition PS_decr_1 (a : nat -> V) (n : nat) : V := a (S n).
Definition PS_decr_n (a : nat -> V) (n k : nat) : V := a (n + k)%nat.
End PS_incr.
Definition PS_mult (a b : nat -> R) n := sum_f_R0 (fun k => a k * b (n - k)%nat) n.
Section PS_opp.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_opp (a : nat -> V) (n : nat) : V := opp (a n).
End PS_opp.
Section PS_minus.
Context {K : AbsRing} {V : NormedModule K}.
Definition PS_minus (a b : nat -> V) (n : nat) : V := plus (a n) (opp (b n)).
End PS_minus.
Definition PS_derive (a : nat -> R) (n : nat) := INR (S n) * a (S n).
Definition PS_derive_n (n : nat) (a : nat -> R) := (fun k => (INR (fact (k + n)%nat) / INR (fact k)) * a (k + n)%nat).

Lemma is_derive_PSeries (a : nat -> R) (x : R) : Rbar_lt (Finite (Rabs x)) (CV_radius a) -> is_derive (PSeries a) x (PSeries (PS_derive a) x).
Proof.
move => Hx.
case: (CV_radius_Reals_2 _ _ Hx) => r0 Hr0 ; rewrite -CV_radius_derive in Hx ; case: (CV_radius_Reals_2 _ _ Hx) => r1 Hr1 ; rewrite CV_radius_derive in Hx.
apply CVU_dom_Reals in Hr0 ; apply CVU_dom_Reals in Hr1.
have Hr : 0 < (Rmin r0 r1).
apply Rmin_case.
by apply r0.
by apply r1.
set D := (Boule x (mkposreal _ Hr)).
assert (Ho : open D).
move => y Hy.
apply Rabs_lt_between' in Hy ; simpl in Hy.
have H : 0 < Rmin ((x+Rmin r0 r1)-y) (y-(x-Rmin r0 r1)).
apply Rmin_case.
rewrite -(Rminus_eq_0 y) ; by apply Rplus_lt_compat_r, Hy.
rewrite -(Rminus_eq_0 ((x-Rmin r0 r1))) /Rminus ; by apply Rplus_lt_compat_r , Hy.
exists (mkposreal _ H) => /= z Hz.
apply Rabs_lt_between' ; split ; apply (Rplus_lt_reg_l (-y)) ; simpl.
apply Ropp_lt_cancel.
apply Rle_lt_trans with (1 := Rabs_maj2 _).
rewrite Ropp_plus_distr ?Ropp_involutive (Rplus_comm (-y)).
apply Rlt_le_trans with (1 := Hz).
exact: Rmin_r.
apply Rle_lt_trans with (1 := Rle_abs _).
rewrite ?(Rplus_comm (-y)).
apply Rlt_le_trans with (1 := Hz).
exact: Rmin_l.
have Hc : is_connected D.
move => x0 y z Hx0 Hy Hx0yz.
rewrite /D.
case: Hx0yz => H1 H2.
apply (Rplus_le_compat_r (-x)) in H1.
apply (Rplus_le_compat_r (-x)) in H2.
move: (conj H1 H2) => {H1 H2} Hxyz.
apply Rabs_le_between_Rmax in Hxyz.
apply Rle_lt_trans with (1 := Hxyz) => /=.
apply Rmax_case.
apply Rle_lt_trans with (1 := Rle_abs _).
exact: Hy.
apply Rle_lt_trans with (1 := Rabs_maj2 _).
exact: Hx0.
have Hfn : CVU_dom (fun (n : nat) (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n) D.
apply CVU_dom_include with (Boule x r0).
move => y Hy.
by apply Rlt_le_trans with (1 := Hy), Rmin_l.
exact: Hr0.
have Idn : (forall (n : nat) (x : R), (0 < n)%nat -> is_derive (fun (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n) x (sum_f_R0 (fun k : nat => (PS_derive a) k * x ^ k) (pred n))).
case => [ y Hn | n y _ ].
by apply lt_irrefl in Hn.
elim: n => [ | n] ; simpl pred ; rewrite /sum_f_R0 -/sum_f_R0.
replace (PS_derive a 0 * y ^ 0) with (0 + a 1%nat * (1 * 1)) by (rewrite /PS_derive /= ; ring).
apply: is_derive_plus.
simpl.
apply: is_derive_const.
apply is_derive_scal.
apply: is_derive_scal_l.
apply: is_derive_id.
move => IH.
apply: is_derive_plus.
apply IH.
rewrite /PS_derive.
replace (INR (S (S n)) * a (S (S n)) * y ^ S n) with (a (S (S n)) * (INR (S (S n)) * y^S n)) by ring.
by apply is_derive_Reals, derivable_pt_lim_scal, derivable_pt_lim_pow.
have Edn : (forall (n : nat) (x : R), D x -> ex_derive (fun (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n) x).
case => [ | n] y Hy.
simpl.
apply: ex_derive_const.
exists (sum_f_R0 (fun k : nat => PS_derive a k * y ^ k) (pred (S n))).
apply (Idn (S n) y).
by apply lt_O_Sn.
have Cdn : (forall (n : nat) (x : R), D x -> continuity_pt (Derive ((fun (n0 : nat) (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n0) n)) x).
have Cdn : (forall (n : nat) (x : R), D x -> continuity_pt (fun x => sum_f_R0 (fun k : nat => PS_derive a k * x ^ k) n) x).
move => n y Hy.
apply derivable_continuous_pt.
elim: n => [ /= | n IH].
exact: derivable_pt_const.
apply derivable_pt_plus ; rewrite -/sum_f_R0.
exact: IH.
apply derivable_pt_scal, derivable_pt_pow.
case => [ | n] y Hy.
simpl ; by apply continuity_pt_const => z.
move => e He ; case: (Cdn n y Hy e He) => {Cdn} d [Hd Cdn].
destruct (Ho y Hy) as [d0 Hd0].
have Hd1 : 0 < Rmin d d0.
apply Rmin_case ; [exact: Hd | by apply d0].
exists (mkposreal _ Hd1) ; split.
exact: Hd1.
move => z Hz ; simpl in Hz.
rewrite (is_derive_unique _ _ _ (Idn (S n) z (lt_O_Sn _))).
rewrite (is_derive_unique _ _ _ (Idn (S n) y (lt_O_Sn _))).
apply (Cdn z) ; split.
by apply Hz.
apply Rlt_le_trans with (1 := proj2 Hz), Rmin_l.
have Hdn : CVU_dom (fun (n : nat) (x : R) => Derive ((fun (n0 : nat) (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n0) n) x) D.
apply CVU_dom_include with (Boule x r1).
move => y Hy.
by apply Rlt_le_trans with (1 := Hy), Rmin_r.
apply CVU_dom_cauchy ; apply CVU_dom_cauchy in Hr1.
move => eps.
case: (Hr1 eps) => {Hr1} N Hr1.
exists (S N) => n m y Hy Hn Hm.
case: n Hn => [ | n] Hn.
by apply le_Sn_O in Hn.
apply le_S_n in Hn.
case: m Hm => [ | m] Hm.
by apply le_Sn_O in Hm.
apply le_S_n in Hm.
rewrite (is_derive_unique _ _ _ (Idn (S n) y (lt_O_Sn _))).
rewrite (is_derive_unique _ _ _ (Idn (S m) y (lt_O_Sn _))).
by apply Hr1.
have Hx' : D x.
by rewrite /D /Boule /= Rminus_eq_0 Rabs_R0.
have H := (CVU_Derive (fun n y => (sum_f_R0 (fun k : nat => a k * y ^ k)) n) D Ho Hc Hfn Edn Cdn Hdn x Hx').
replace (PSeries (PS_derive a) x) with (real (Lim_seq (fun n : nat => Derive (fun y : R => sum_f_R0 (fun k : nat => a k * y ^ k) n) x))).
apply: is_derive_ext H.
simpl => t.
apply (f_equal real), Lim_seq_ext.
intros n; apply sym_eq, sum_n_Reals.
rewrite -Lim_seq_incr_1.
apply (f_equal real), Lim_seq_ext => n.
rewrite sum_n_Reals.
apply is_derive_unique, Idn.
by apply lt_O_Sn.
move => y Hy.
apply sym_eq.
apply is_lim_seq_unique.
apply is_lim_seq_spec.
move => eps.
case: (Hr1 eps (cond_pos eps)) => {Hr1} N Hr1.
exists N => n Hn.
rewrite -Rabs_Ropp Ropp_minus_distr'.
by apply Hr1.
move => y Hy.
apply sym_eq.
apply is_lim_seq_unique.
apply is_lim_seq_spec.
move => eps.
case: (Hr0 eps (cond_pos eps)) => {Hr0} N Hr0.
exists N => n Hn.
rewrite -Rabs_Ropp Ropp_minus_distr'.
by apply Hr0.
move => y Hy.
apply sym_eq.
apply is_lim_seq_unique.
apply is_lim_seq_spec.
move => eps.
case: (Hr1 eps (cond_pos eps)) => {Hr1} N Hr1.
exists N => n Hn.
rewrite -Rabs_Ropp Ropp_minus_distr'.
by apply Hr1.

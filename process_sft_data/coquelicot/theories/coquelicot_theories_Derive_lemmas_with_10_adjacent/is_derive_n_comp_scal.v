Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Lim_seq Iter.
Require Import Hierarchy Continuity Equiv.
Open Scope R_scope.
Section LinearFct.
Context {K : AbsRing} {U V : NormedModule K}.
Record is_linear (l : U -> V) := { linear_plus : forall (x y : U), l (plus x y) = plus (l x) (l y) ; linear_scal : forall (k : K) (x : U), l (scal k x) = scal k (l x) ; linear_norm : exists M : R, 0 < M /\ (forall x : U, norm (l x) <= M * norm x) }.
End LinearFct.
Section Op_LinearFct.
Context {K : AbsRing} {V : NormedModule K}.
End Op_LinearFct.
Section Linear_domin.
Context {T : Type} {Kw K : AbsRing} {W : NormedModule Kw} {U V : NormedModule K}.
End Linear_domin.
Section Diff.
Context {K : AbsRing} {U : NormedModule K} {V : NormedModule K}.
Definition filterdiff (f : U -> V) F (l : U -> V) := is_linear l /\ forall x, is_filter_lim F x -> is_domin F (fun y : U => minus y x) (fun y => minus (minus (f y) (f x)) (l (minus y x))).
Definition ex_filterdiff (f : U -> V) F := exists (l : U -> V), filterdiff f F l.
End Diff.
Section Diff_comp.
Context {K : AbsRing} {U V W : NormedModule K}.
End Diff_comp.
Section Diff_comp2.
Context {K : AbsRing} {T U V : NormedModule K}.
Section Diff_comp2'.
Context {W : NormedModule K}.
End Diff_comp2'.
Context {W : NormedModule K}.
End Diff_comp2.
Section Operations.
Context {K : AbsRing} {V : NormedModule K}.
Local Ltac plus_grab e := repeat rewrite (plus_assoc _ e) -(plus_comm e) -(plus_assoc e).
End Operations.
Section Operations_fct.
Context {K : AbsRing} {U V : NormedModule K}.
End Operations_fct.
Section Derive.
Context {K : AbsRing} {V : NormedModule K}.
Definition is_derive (f : K -> V) (x : K) (l : V) := filterdiff f (locally x) (fun y : K => scal y l).
Definition ex_derive (f : K -> V) (x : K) := exists l : V, is_derive f x l.
End Derive.
Definition Derive (f : R -> R) (x : R) := real (Lim (fun h => (f (x+h) - f x)/h) 0).
Section Extensionality.
Context {K : AbsRing} {V : NormedModule K}.
End Extensionality.
Section Const.
Context {K : AbsRing} {V : NormedModule K}.
End Const.
Section Id.
Context {K : AbsRing}.
End Id.
Section Opp.
Context {K : AbsRing} {V : NormedModule K}.
End Opp.
Section Plus.
Context {K : AbsRing} {V : NormedModule K}.
End Plus.
Section Minus.
Context {K : AbsRing} {V : NormedModule K}.
End Minus.
Section Scal_l.
Context {K : AbsRing} {V : NormedModule K}.
End Scal_l.
Section Comp.
Context {K : AbsRing} {V : NormedModule K}.
End Comp.
Section ext_cont.
Context {U : UniformSpace}.
Definition extension_cont (f g : R -> U) (a x : R) : U := match Rle_dec x a with | left _ => f x | right _ => g x end.
End ext_cont.
Section ext_cont'.
Context {V : NormedModule R_AbsRing}.
End ext_cont'.
Section ext_C0.
Context {V : NormedModule R_AbsRing}.
Definition extension_C0 (f : R -> V) (a b : Rbar) (x : R) : V := match Rbar_le_dec a x with | left _ => match Rbar_le_dec x b with | left _ => f x | right _ => f (real b) end | right _ => f (real a) end.
End ext_C0.
Section ext_C1.
Context {V : NormedModule R_AbsRing}.
Definition extension_C1 (f df : R -> V) (a b : Rbar) (x : R) : V := match Rbar_le_dec a x with | left _ => match Rbar_le_dec x b with | left _ => f x | right _ => plus (f (real b)) (scal (x - real b) (df (real b))) end | right _ => plus (f (real a)) (scal (x - real a) (df (real a))) end.
End ext_C1.
Section NullDerivative.
Context {V : NormedModule R_AbsRing}.
End NullDerivative.
Fixpoint Derive_n (f : R -> R) (n : nat) x := match n with | O => f x | S n => Derive (Derive_n f n) x end.
Definition ex_derive_n f n x := match n with | O => True | S n => ex_derive (Derive_n f n) x end.
Definition is_derive_n f n x l := match n with | O => f x = l | S n => is_derive (Derive_n f n) x l end.

Lemma ex_derive_n_minus (f g : R -> R) (n : nat) (x : R) : locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) -> locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) -> ex_derive_n (fun x => f x - g x) n x.
Proof.
move => Hf Hg.
apply ex_derive_n_plus.
by [].
move: Hg ; apply filter_imp => y Hg k Hk.
Admitted.

Lemma is_derive_n_minus (f g : R -> R) (n : nat) (x lf lg : R) : locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) -> locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) -> is_derive_n f n x lf -> is_derive_n g n x lg -> is_derive_n (fun x => f x - g x) n x (lf - lg).
Proof.
move => Hf Hg Df Dg.
apply is_derive_n_plus.
by [].
move: Hg ; apply filter_imp => y Hg k Hk.
apply ex_derive_n_opp ; by apply Hg.
by [].
Admitted.

Lemma Derive_n_scal_l (f : R -> R) (n : nat) (a x : R) : Derive_n (fun y => a * f y) n x = a * Derive_n f n x.
Proof.
elim: n x => /= [ | n IH] x.
by [].
rewrite -Derive_scal.
Admitted.

Lemma ex_derive_n_scal_l (f : R -> R) (n : nat) (a x : R) : ex_derive_n f n x -> ex_derive_n (fun y => a * f y) n x.
Proof.
case: n x => /= [ | n] x Hf.
by [].
apply ex_derive_ext with (fun y => a * Derive_n f n y).
move => t ; by rewrite Derive_n_scal_l.
Admitted.

Lemma is_derive_n_scal_l (f : R -> R) (n : nat) (a x l : R) : is_derive_n f n x l -> is_derive_n (fun y => a * f y) n x (a * l).
Proof.
case: n x => /= [ | n] x Hf.
by rewrite Hf.
eapply filterdiff_ext_lin.
apply filterdiff_ext with (fun y => a * Derive_n f n y).
move => t ; by rewrite Derive_n_scal_l.
apply @filterdiff_scal_r_fct ; try by apply locally_filter.
by apply Rmult_comm.
apply Hf.
move => /= y.
rewrite /scal /= /mult /=.
Admitted.

Lemma Derive_n_scal_r (f : R -> R) (n : nat) (a x : R) : Derive_n (fun y => f y * a) n x = Derive_n f n x * a.
Proof.
rewrite Rmult_comm -Derive_n_scal_l.
Admitted.

Lemma ex_derive_n_scal_r (f : R -> R) (n : nat) (a x : R) : ex_derive_n f n x -> ex_derive_n (fun y => f y * a) n x.
Proof.
move/(ex_derive_n_scal_l _ _ a).
Admitted.

Lemma is_derive_n_scal_r (f : R -> R) (n : nat) (a x l : R) : is_derive_n f n x l -> is_derive_n (fun y => f y * a) n x (l * a).
Proof.
move/(is_derive_n_scal_l _ _ a).
rewrite Rmult_comm.
Admitted.

Lemma Derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x : R) : locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) -> Derive_n (fun y => f (a * y)) n x = (a ^ n * Derive_n f n (a * x)).
Proof.
case: (Req_dec a 0) => [ -> _ | Ha] /=.
rewrite Rmult_0_l.
elim: n x => [ | n IH] x /= ; rewrite ?Rmult_0_l.
ring.
rewrite (Derive_ext _ _ _ IH).
by apply Derive_const.
move => Hf.
apply (locally_singleton _ (fun x => Derive_n (fun y : R => f (a * y)) n x = a ^ n * Derive_n f n (a * x))).
elim: n Hf => [ | n IH] Hf.
apply filter_forall => /= y ; ring.
case: IH => [ | r IH].
case: Hf => r0 Hf.
exists r0 => y Hy k Hk ; by intuition.
case: Hf => r0 Hf.
have Hr1 : 0 < Rmin (r0 / (Rabs a)) r.
apply Rmin_case.
apply Rdiv_lt_0_compat.
by apply r0.
by apply Rabs_pos_lt.
by apply r.
set r1 := mkposreal _ Hr1.
exists r1 => y Hy /=.
rewrite (Derive_ext_loc _ (fun y => a ^ n * Derive_n f n (a * y))).
rewrite Derive_scal.
rewrite (Rmult_comm a (a^n)) Rmult_assoc.
apply f_equal.
rewrite Derive_comp.
rewrite (Derive_ext (Rmult a) (fun x => a * x)) => //.
rewrite Derive_scal Derive_id ; ring.
apply Hf with (k := S n).
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /=.
rewrite -/(Rminus _ _) -Rmult_minus_distr_l Rabs_mult.
apply Rlt_le_trans with (Rabs a * r1).
apply Rmult_lt_compat_l.
by apply Rabs_pos_lt.
by apply Hy.
rewrite Rmult_comm ; apply Rle_div_r.
by apply Rabs_pos_lt.
rewrite /r1 ; by apply Rmin_l.
by apply lt_n_Sn.
apply ex_derive_scal.
by apply ex_derive_id.
rewrite /ball /= /AbsRing_ball /= in Hy.
apply Rabs_lt_between' in Hy.
case: Hy => Hy1 Hy2.
apply Rlt_Rminus in Hy1.
apply Rlt_Rminus in Hy2.
have Hy : 0 < Rmin (y - (x - r1)) (x + r1 - y).
by apply Rmin_case.
exists (mkposreal (Rmin (y - (x - r1)) (x + r1 - y)) Hy).
set r2 := Rmin (y - (x - r1)) (x + r1 - y).
move => t Ht.
apply IH.
apply Rabs_lt_between'.
rewrite /ball /= /AbsRing_ball /= in Ht.
apply Rabs_lt_between' in Ht.
simpl in Ht.
split.
apply Rle_lt_trans with (2 := proj1 Ht).
rewrite /r2 ; apply Rle_trans with (y-(y-(x-r1))).
ring_simplify ; apply Rplus_le_compat_l, Ropp_le_contravar.
rewrite /r1 ; apply Rmin_r.
apply Rplus_le_compat_l, Ropp_le_contravar, Rmin_l.
apply Rlt_le_trans with (1 := proj2 Ht).
rewrite /r2 ; apply Rle_trans with (y+((x+r1)-y)).
apply Rplus_le_compat_l, Rmin_r.
ring_simplify ; apply Rplus_le_compat_l.
Admitted.

Lemma ex_derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x : R) : locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) -> ex_derive_n (fun y => f (a * y)) n x.
Proof.
case: n f x => /= [ | n] f x Hf.
by [].
case: (Req_dec a 0) => Ha.
rewrite Ha => {a Ha Hf}.
apply ex_derive_ext with (fun _ => Derive_n (fun y : R => f (0 * y)) n 0).
elim: n => /= [ | n IH] t.
by rewrite ?Rmult_0_l.
rewrite -?(Derive_ext _ _ _ IH).
by rewrite ?Derive_const.
by apply ex_derive_const.
apply ex_derive_ext_loc with (fun x => a^n * Derive_n f n (a * x)).
case: Hf => r Hf.
have Hr0 : 0 < r / Rabs a.
apply Rdiv_lt_0_compat.
by apply r.
by apply Rabs_pos_lt.
exists (mkposreal _ Hr0) => /= y Hy.
apply eq_sym, Derive_n_comp_scal.
have : Rabs (a*y - a*x) < r.
rewrite -Rmult_minus_distr_l Rabs_mult.
replace (pos r) with (Rabs a * (r / Rabs a)) by (field ; by apply Rgt_not_eq, Rabs_pos_lt).
apply Rmult_lt_compat_l.
by apply Rabs_pos_lt.
by apply Hy.
move => {Hy} Hy.
apply Rabs_lt_between' in Hy ; case: Hy => Hy1 Hy2.
apply Rlt_Rminus in Hy1.
apply Rlt_Rminus in Hy2.
exists (mkposreal _ (Rmin_pos _ _ Hy1 Hy2)) => /= z Hz k Hk.
rewrite /ball /= /AbsRing_ball /= in Hz.
apply Rabs_lt_between' in Hz ; case: Hz => Hz1 Hz2.
rewrite /Rminus -Rmax_opp_Rmin in Hz1.
rewrite Rplus_min_distr_l in Hz2.
apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2.
ring_simplify in Hz2.
rewrite Rplus_max_distr_l in Hz1.
apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1.
ring_simplify in Hz1.
apply Hf.
apply Rabs_lt_between' ; by split.
by intuition.
apply ex_derive_scal.
apply ex_derive_comp.
apply (locally_singleton _ _) in Hf.
by apply Hf with (k := S n).
Admitted.

Lemma Derive_n_comp_opp (f : R -> R) (n : nat) (x : R) : locally (- x) (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) -> Derive_n (fun y => f (- y)) n x = ((-1) ^ n * Derive_n f n (-x)).
Proof.
move => Hf.
rewrite -(Derive_n_ext (fun y : R => f (-1 * y))).
rewrite (Derive_n_comp_scal f (-1) n x).
by replace (-1*x) with (-x) by ring.
by replace (-1*x) with (-x) by ring.
Admitted.

Lemma ex_derive_n_comp_opp (f : R -> R) (n : nat) (x : R) : locally (- x) (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) -> ex_derive_n (fun y => f (- y)) n x.
Proof.
move => Hf.
apply (ex_derive_n_ext (fun y : R => f (-1 * y))).
move => t ; by ring_simplify (-1*t).
apply (ex_derive_n_comp_scal f (-1) n x).
Admitted.

Lemma is_derive_n_comp_opp (f : R -> R) (n : nat) (x l : R) : locally (- x) (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) -> is_derive_n f n (-x) l -> is_derive_n (fun y => f (- y)) n x ((-1)^n * l).
Proof.
move => Hfn Hf.
apply (is_derive_n_ext (fun y : R => f (-1 * y))).
move => t ; by ring_simplify (-1*t).
apply (is_derive_n_comp_scal f (-1) n x).
by replace (-1*x) with (-x) by ring.
Admitted.

Lemma Derive_n_comp_trans (f : R -> R) (n : nat) (x b : R) : Derive_n (fun y => f (y + b)) n x = Derive_n f n (x + b).
Proof.
elim: n x => [ | n IH] x /=.
by [].
rewrite (Derive_ext _ _ _ IH) => {IH}.
generalize (Derive_n f n) => {f} f.
apply (f_equal real).
apply Lim_ext => y.
replace (x + b + y) with (x + y + b) by ring.
Admitted.

Lemma ex_derive_n_comp_trans (f : R -> R) (n : nat) (x b : R) : ex_derive_n f n (x + b) -> ex_derive_n (fun y => f (y + b)) n x.
Proof.
case: n => [ | n] /= Df.
by [].
apply ex_derive_ext with (fun x => Derive_n f n (x + b)).
simpl => t.
apply sym_eq, Derive_n_comp_trans.
move: (Derive_n f n) Df => {f} f Df.
apply ex_derive_comp.
apply Df.
apply: ex_derive_plus.
apply ex_derive_id.
Admitted.

Lemma is_derive_n_comp_trans (f : R -> R) (n : nat) (x b l : R) : is_derive_n f n (x + b) l -> is_derive_n (fun y => f (y + b)) n x l.
Proof.
case: n => [ | n] /= Df.
by [].
apply is_derive_ext with (fun x => Derive_n f n (x + b)).
simpl => t.
apply sym_eq, Derive_n_comp_trans.
move: (Derive_n f n) Df => {f} f Df.
eapply filterdiff_ext_lin.
apply @filterdiff_comp'.
apply @filterdiff_plus_fct ; try by apply locally_filter.
by apply filterdiff_id.
by apply filterdiff_const.
by apply Df.
simpl => y.
Admitted.

Theorem Taylor_Lagrange : forall f n x y, x < y -> ( forall t, x <= t <= y -> forall k, (k <= S n)%nat -> ex_derive_n f k t ) -> exists zeta, x < zeta < y /\ f y = sum_f_R0 (fun m => (y-x) ^ m / INR (fact m) * Derive_n f m x ) n + (y-x) ^ (S n) / INR (fact (S n)) * Derive_n f (S n) zeta.
Proof.
intros f n x y Hxy Df.
pose (c:= (f y - sum_f_R0 (fun m => (y-x) ^ m / INR (fact m) * Derive_n f m x ) n) / (y-x) ^ (S n)).
pose (g t := f y - sum_f_R0 (fun m => (y-t) ^ m / INR (fact m) * Derive_n f m t ) n - c * (y-t) ^ (S n)).
assert (Dg : forall t, x <= t <= y -> is_derive g t (- (y-t) ^ n / INR (fact n) * Derive_n f (S n) t + c * INR (S n) * (y-t) ^ n)).
intros t Ht.
unfold g.
assert (Dp: forall n, derivable_pt_lim (fun x0 : R => (y - x0) ^ S n) t (INR (S n) * (y - t) ^ n * (0 - 1))).
intros m.
apply (derivable_pt_lim_comp (fun t => y - t) (fun t => t ^ (S m))).
apply derivable_pt_lim_minus.
apply derivable_pt_lim_const.
apply derivable_pt_lim_id.
apply derivable_pt_lim_pow.
apply: is_derive_plus.
clear c g.
rename n into N.
generalize (le_refl N).
generalize N at -2.
intros n Hn.
move: Hn.
induction n.
intros _.
simpl.
eapply filterdiff_ext_lin.
apply @filterdiff_minus_fct ; try by apply locally_filter.
apply filterdiff_const.
apply @filterdiff_scal_r_fct with (f := fun u => f u).
by apply locally_filter.
by apply Rmult_comm.
apply Derive_correct.
apply (Df t Ht 1%nat).
apply le_n_S.
apply le_0_n.
simpl => z.
rewrite /minus /plus /opp /zero /scal /= /mult /=.
field.
intros Hn.
apply filterdiff_ext with (fun x0 : R => (f y - (sum_f_R0 (fun m : nat => (y - x0) ^ m / INR (fact m) * Derive_n f m x0) n)) - (y - x0) ^ (S n) / INR (fact (S n)) * Derive_n f (S n) x0).
simpl.
intros; ring.
eapply filterdiff_ext_lin.
apply @filterdiff_plus_fct ; try by apply locally_filter.
apply IHn.
now apply lt_le_weak.
apply @filterdiff_opp_fct ; try by apply locally_filter.
generalize (filterdiff_mult_fct (fun x0 => ((y - x0) ^ S n / INR (fact (S n)))) (fun x0 => Derive_n f (S n) x0)) => /= H.
apply H ; clear H.
by apply Rmult_comm.
apply @filterdiff_scal_l_fct ; try by apply locally_filter.
generalize (filterdiff_comp' (fun u => y - u) (fun x => pow x (S n))) => /= H ; apply H ; clear H.
apply @filterdiff_minus_fct ; try apply locally_filter.
apply filterdiff_const.
apply filterdiff_id.
apply is_derive_Reals.
apply (derivable_pt_lim_pow _ (S n)).
apply Derive_correct.
apply (Df t Ht (S (S n))).
now apply le_n_S.
move => z.
change (fact (S n)) with ((S n)*fact n)%nat.
rewrite mult_INR.
set v := INR (S n).
rewrite /minus /plus /opp /zero /scal /= /mult /=.
field.
split.
apply INR_fact_neq_0.
now apply not_0_INR.
eapply filterdiff_ext_lin.
apply filterdiff_ext with (fun x0 : R => -c * (y - x0) ^ S n).
simpl => z ; ring.
apply @filterdiff_scal_r_fct ; try by apply locally_filter.
by apply Rmult_comm.
apply is_derive_Reals, Dp.
set v := INR (S n).
simpl => z.
rewrite /scal /= /mult /=.
ring.
assert (Dg' : forall t : R, x <= t <= y -> derivable_pt g t).
intros t Ht.
exists (Derive g t).
apply is_derive_Reals.
apply Derive_correct.
eexists.
apply (Dg t Ht).
assert (pr : forall t : R, x < t < y -> derivable_pt g t).
intros t Ht.
apply Dg'.
split ; now apply Rlt_le.
assert (Zxy: (y - x) ^ (S n) <> 0).
apply pow_nonzero.
apply Rgt_not_eq.
apply Rplus_gt_reg_l with x.
now ring_simplify.
destruct (Rolle g x y pr) as (zeta, (Hzeta1,Hzeta2)).
intros t Ht.
apply derivable_continuous_pt.
now apply Dg'.
exact Hxy.
apply trans_eq with 0.
unfold g, c.
now field.
unfold g.
destruct n.
simpl; field.
rewrite decomp_sum.
rewrite sum_eq_R0.
simpl; field.
intros; simpl; field.
exact (INR_fact_neq_0 (S n0)).
apply lt_0_Sn.
exists zeta.
apply (conj Hzeta1).
rewrite Rmult_assoc.
replace (/ INR (fact (S n)) * Derive_n f (S n) zeta) with c.
unfold c.
now field.
apply Rmult_eq_reg_r with (INR (S n) * (y - zeta) ^ n).
apply Rplus_eq_reg_l with ((- (y - zeta) ^ n / INR (fact n) * Derive_n f (S n) zeta)).
change (fact (S n)) with (S n * fact n)%nat.
rewrite mult_INR.
apply trans_eq with 0.
rewrite -Rmult_assoc.
assert (H: x <= zeta <= y) by (split ; apply Rlt_le ; apply Hzeta1).
rewrite -(is_derive_unique _ _ _ (Dg _ H)).
destruct (pr zeta Hzeta1) as (x0,Hd).
simpl in Hzeta2.
rewrite Hzeta2 in Hd.
now apply is_derive_unique, is_derive_Reals.
field.
split.
apply INR_fact_neq_0.
now apply not_0_INR.
apply Rmult_integral_contrapositive_currified.
now apply not_0_INR.
apply pow_nonzero.
apply Rgt_not_eq.
apply Rplus_gt_reg_l with zeta.
ring_simplify.
Admitted.

Lemma is_derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x l : R) : locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) -> is_derive_n f n (a * x) l -> is_derive_n (fun y => f (a * y)) n x (a ^ n * l).
Proof.
case: n => /= [ | n] Hfn Hf.
by rewrite Rmult_1_l.
apply is_derive_unique in Hf.
rewrite -Hf.
rewrite -(Derive_n_comp_scal f a (S n) x) => //.
apply Derive_correct.
by apply (ex_derive_n_comp_scal f a (S n) x).

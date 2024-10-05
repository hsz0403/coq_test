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

Lemma ex_derive_id : forall x : K, ex_derive (fun t : K => t) x.
Proof.
intros x.
eexists.
Admitted.

Lemma Derive_id : forall x, Derive id x = 1.
Proof.
intros x.
apply is_derive_unique.
Admitted.

Lemma is_derive_opp : forall (f : K -> V) (x : K) (l : V), is_derive f x l -> is_derive (fun x => opp (f x)) x (opp l).
Proof.
intros f x l Df.
apply filterdiff_ext_lin with (fun t : K => opp (scal t l)).
apply filterdiff_comp' with (1 := Df).
apply filterdiff_opp.
intros y.
apply sym_eq.
Admitted.

Lemma ex_derive_opp : forall (f : K -> V) (x : K), ex_derive f x -> ex_derive (fun x => opp (f x)) x.
Proof.
intros f x [df Df].
eexists.
apply is_derive_opp.
Admitted.

Lemma Derive_opp : forall f x, Derive (fun x => - f x) x = - Derive f x.
Proof.
intros f x.
unfold Derive, Lim.
rewrite /Rbar_loc_seq.
rewrite -Rbar.Rbar_opp_real.
rewrite -Lim_seq_opp.
apply f_equal, Lim_seq_ext => n.
rewrite -Ropp_mult_distr_l_reverse.
apply (f_equal (fun v => v / _)).
Admitted.

Lemma is_derive_plus : forall (f g : K -> V) (x : K) (df dg : V), is_derive f x df -> is_derive g x dg -> is_derive (fun x => plus (f x) (g x)) x (plus df dg).
Proof.
intros f g x df dg Df Dg.
eapply filterdiff_ext_lin.
apply filterdiff_plus_fct ; try eassumption.
simpl => y.
Admitted.

Lemma ex_derive_plus : forall (f g : K -> V) (x : K), ex_derive f x -> ex_derive g x -> ex_derive (fun x => plus (f x) (g x)) x.
Proof.
intros f g x [df Df] [dg Dg].
exists (plus df dg).
Admitted.

Lemma is_derive_sum_n : forall (f : nat -> K -> V) (n : nat) (x : K) (d : nat -> V), (forall k, (k <= n)%nat -> is_derive (f k) x (d k)) -> is_derive (fun y => sum_n (fun k => f k y) n) x (sum_n d n).
Proof.
intros f n x d.
elim: n => /= [ | n IH] Hf.
rewrite sum_O.
eapply is_derive_ext, (Hf O) => //.
intros t ; by rewrite sum_O.
eapply is_derive_ext.
intros t ; apply sym_eq, sum_Sn.
rewrite sum_Sn.
apply is_derive_plus.
apply IH => k Hk.
by apply Hf, le_trans with (1 := Hk), le_n_Sn.
Admitted.

Lemma ex_derive_sum_n : forall (f : nat -> K -> V) (n : nat) (x : K), (forall k, (k <= n)%nat -> ex_derive (f k) x) -> ex_derive (fun y => sum_n (fun k => f k y) n) x.
Proof.
intros f n x.
elim: n => /= [ | n IH] Hf.
eapply ex_derive_ext.
intros t ; by rewrite sum_O.
by apply (Hf O).
eapply ex_derive_ext.
intros t ; by rewrite sum_Sn.
apply ex_derive_plus.
apply IH => k Hk.
by apply Hf, le_trans with (1 := Hk), le_n_Sn.
Admitted.

Lemma Derive_plus : forall f g x, ex_derive f x -> ex_derive g x -> Derive (fun x => f x + g x) x = Derive f x + Derive g x.
Proof.
intros f g x Df Dg.
apply is_derive_unique.
Admitted.

Lemma Derive_sum_n (f : nat -> R -> R) (n : nat) (x : R) : (forall k, (k <= n)%nat -> ex_derive (f k) x) -> Derive (fun y => sum_n (fun k => f k y) n) x = sum_n (fun k => Derive (f k) x) n.
Proof.
move => Hf.
apply is_derive_unique.
apply: is_derive_sum_n.
move => k Hk.
Admitted.

Lemma is_derive_minus : forall (f g : K -> V) (x : K) (df dg : V), is_derive f x df -> is_derive g x dg -> is_derive (fun x => minus (f x) (g x)) x (minus df dg).
Proof.
intros f g x df dg Df Dg.
eapply filterdiff_ext_lin.
apply filterdiff_minus_fct ; try eassumption.
simpl => y.
Admitted.

Lemma ex_derive_minus : forall (f g : K -> V) (x : K), ex_derive f x -> ex_derive g x -> ex_derive (fun x => minus (f x) (g x)) x.
Proof.
intros f g x [df Df] [dg Dg].
exists (minus df dg).
Admitted.

Lemma Derive_minus : forall f g x, ex_derive f x -> ex_derive g x -> Derive (fun x => f x - g x) x = Derive f x - Derive g x.
Proof.
intros f g x Df Dg.
apply is_derive_unique.
Admitted.

Lemma is_derive_inv (f : R -> R) (x l : R) : is_derive f x l -> f x <> 0 -> is_derive (fun y : R => / f y) x (-l/(f x)^2).
Proof.
move => Hf Hl.
eapply filterdiff_ext_lin.
apply filterdiff_ext with (fun y => 1/f y).
move => t ; by rewrite /Rdiv Rmult_1_l.
apply is_derive_Reals.
apply derivable_pt_lim_div.
apply derivable_pt_lim_const.
apply is_derive_Reals.
exact Hf.
exact Hl.
simpl => y ; apply f_equal.
Admitted.

Lemma ex_derive_inv (f : R -> R) (x : R) : ex_derive f x -> f x <> 0 -> ex_derive (fun y : R => / f y) x.
Proof.
case => l Hf Hl.
exists (-l/(f x)^2).
Admitted.

Lemma Derive_inv (f : R -> R) (x : R) : ex_derive f x -> f x <> 0 -> Derive (fun y => / f y) x = - Derive f x / (f x) ^ 2.
Proof.
move/Derive_correct => Hf Hl.
apply is_derive_unique.
Admitted.

Lemma is_derive_scal : forall (f : R -> R) (x k df : R), is_derive f x df -> is_derive (fun x : R => k * f x) x (k * df).
Proof.
intros f x k df Df.
change Rmult with (scal (V := R_NormedModule)).
eapply filterdiff_ext_lin.
apply filterdiff_scal_r_fct with (2 := Df).
apply Rmult_comm.
rewrite /scal /= /mult /= => y.
Admitted.

Lemma ex_derive_scal : forall (f : R -> R) (k x : R), ex_derive f x -> ex_derive (fun x : R => k * f x) x.
Proof.
intros f k x (df,Df).
exists (k * df).
Admitted.

Lemma Derive_scal : forall f k x, Derive (fun x => k * f x) x = k * Derive f x.
Proof.
intros f k x.
unfold Derive, Lim.
have H : (forall x, k * Rbar.real x = Rbar.real (Rbar.Rbar_mult (Rbar.Finite k) x)).
case: (Req_dec k 0) => [-> | Hk].
case => [l | | ] //= ; rewrite Rmult_0_l.
case: Rle_dec (Rle_refl 0) => //= H _.
case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
case: Rle_dec (Rle_refl 0) => //= H _.
case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
case => [l | | ] //= ; rewrite Rmult_0_r.
case: Rle_dec => //= H.
case: Rle_lt_or_eq_dec => //=.
case: Rle_dec => //= H.
case: Rle_lt_or_eq_dec => //=.
rewrite H.
rewrite -Lim_seq_scal_l.
apply f_equal, Lim_seq_ext => n.
rewrite -Rmult_assoc.
apply (f_equal (fun v => v / _)).
Admitted.

Lemma ex_derive_scal_l : forall (f : K -> K) (x : K) (k : V), ex_derive f x -> ex_derive (fun x => scal (f x) k) x.
Proof.
intros f x k [df Df].
exists (scal df k).
Admitted.

Lemma Derive_scal_l (f : R -> R) (k x : R) : Derive (fun x => f x * k) x = Derive f x * k.
Proof.
rewrite Rmult_comm -Derive_scal.
Admitted.

Lemma is_derive_mult : forall (f g : R -> R) (x : R) (df dg : R), is_derive f x df -> is_derive g x dg -> is_derive (fun t : R => f t * g t) x (df * g x + f x * dg) .
Proof.
intros f g x df dg Df Dg.
eapply filterdiff_ext_lin.
apply @filterdiff_mult_fct with (2 := Df) (3 := Dg).
exact Rmult_comm.
rewrite /scal /= /mult /plus /= => y.
Admitted.

Lemma ex_derive_mult (f g : R -> R) (x : R) : ex_derive f x -> ex_derive g x -> ex_derive (fun x : R => f x * g x) x.
Proof.
move => [d1 H1] [d2 H2].
exists (d1 * g x + f x * d2).
Admitted.

Lemma Derive_mult (f g : R -> R) (x : R) : ex_derive f x -> ex_derive g x -> Derive (fun x => f x * g x) x = Derive f x * g x + f x * Derive g x.
Proof.
move => H1 H2.
apply is_derive_unique.
Admitted.

Lemma is_derive_pow (f : R -> R) (n : nat) (x : R) (l : R) : is_derive f x l -> is_derive (fun x : R => (f x)^n) x (INR n * l * (f x)^(pred n)).
Proof.
move => H.
rewrite (Rmult_comm _ l) Rmult_assoc Rmult_comm.
apply is_derive_Reals.
apply (derivable_pt_lim_comp f (fun x => x^n)).
now apply is_derive_Reals.
Admitted.

Lemma ex_derive_pow (f : R -> R) (n : nat) (x : R) : ex_derive f x -> ex_derive (fun x : R => (f x)^n) x.
Proof.
case => l H.
exists (INR n * l * (f x)^(pred n)).
Admitted.

Lemma Derive_pow (f : R -> R) (n : nat) (x : R) : ex_derive f x -> Derive (fun x => (f x)^n) x = (INR n * Derive f x * (f x)^(pred n)).
Proof.
move => H.
apply is_derive_unique.
apply is_derive_pow.
Admitted.

Lemma is_derive_div : forall (f g : R -> R) (x : R) (df dg : R), is_derive f x df -> is_derive g x dg -> g x <> 0 -> is_derive (fun t : R => f t / g t) x ((df * g x - f x * dg) / (g x ^ 2)).
Proof.
intros f g x df dg Df Dg Zgx.
evar_last.
apply is_derive_mult.
exact Df.
apply is_derive_inv with (2 := Zgx).
exact Dg.
simpl.
Admitted.

Lemma ex_derive_div (f g : R -> R) (x : R) : ex_derive f x -> ex_derive g x -> g x <> 0 -> ex_derive (fun y => f y / g y) x.
Proof.
move => Hf Hg Hl.
apply ex_derive_mult.
apply Hf.
Admitted.

Lemma Derive_div (f g : R -> R) (x : R) : ex_derive f x -> ex_derive g x -> g x <> 0 -> Derive (fun y => f y / g y) x = (Derive f x * g x - f x * Derive g x) / (g x) ^ 2.
Proof.
move => Hf Hg Hl.
apply is_derive_unique.
Admitted.

Lemma is_derive_comp : forall (f : K -> V) (g : K -> K) (x : K) (df : V) (dg : K), is_derive f (g x) df -> is_derive g x dg -> is_derive (fun x => f (g x)) x (scal dg df).
Proof.
intros f g x df dg Df Dg.
eapply filterdiff_ext_lin.
apply filterdiff_comp' with (1 := Dg) (2 := Df).
simpl => y.
Admitted.

Lemma ex_derive_comp : forall (f : K -> V) (g : K -> K) (x : K), ex_derive f (g x) -> ex_derive g x -> ex_derive (fun x => f (g x)) x.
Proof.
intros f g x [df Df] [dg Dg].
exists (scal dg df).
Admitted.

Lemma Derive_comp (f g : R -> R) (x : R) : ex_derive f (g x) -> ex_derive g x -> Derive (fun x => f (g x)) x = Derive g x * Derive f (g x).
Proof.
intros Df Dg.
apply is_derive_unique.
Admitted.

Lemma MVT_gen (f : R -> R) (a b : R) (df : R -> R) : let a0 := Rmin a b in let b0 := Rmax a b in (forall x, a0 < x < b0 -> is_derive f x (df x)) -> (forall x, a0 <= x <= b0 -> continuity_pt f x) -> exists c, a0 <= c <= b0 /\ f b - f a = df c * (b - a).
Proof.
move => a0 b0 Hd Hf.
case: (Req_dec a0 b0) => Hab.
exists a0 ; split.
split ; by apply Req_le.
replace b with a.
ring.
move: Hab ; rewrite /a0 /b0 /Rmin /Rmax ; by case: Rle_dec => Hab.
have pr1 : forall c:R, a0 < c < b0 -> derivable_pt f c.
move => x Hx ; exists (df x).
by apply is_derive_Reals, Hd.
have pr2 : forall c:R, a0 < c < b0 -> derivable_pt id c.
move => x Hx ; exists 1.
by apply derivable_pt_lim_id.
case: (MVT f id a0 b0 pr1 pr2).
apply Rnot_le_lt ; contradict Hab ; apply Rle_antisym.
by apply Rcomplements.Rmin_Rmax.
by apply Hab.
by apply Hf.
move => x Hx ; apply derivable_continuous, derivable_id.
move => /= c [Hc H].
exists c ; split.
split ; by apply Rlt_le, Hc.
replace (df c) with (derive_pt f c (pr1 c Hc)).
move: H ; rewrite {1 2}/id /a0 /b0 /Rmin /Rmax ; case: Rle_dec => Hab0 H.
rewrite Rmult_comm H -(pr_nu _ _ (derivable_pt_id _)) derive_pt_id.
ring.
replace (derive_pt f c (pr1 c Hc) * (b - a)) with (-((a - b) * derive_pt f c (pr1 c Hc))) by ring.
rewrite H -(pr_nu _ _ (derivable_pt_id _)) derive_pt_id.
ring.
case: (pr1 c Hc) => /= l Hl.
transitivity (Derive f c).
apply sym_eq, is_derive_unique, is_derive_Reals, Hl.
Admitted.

Lemma incr_function (f : R -> R) (a b : Rbar) (df : R -> R) : (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> is_derive f x (df x)) -> ((forall (x : R), Rbar_lt a x -> Rbar_lt x b -> df x > 0) -> (forall (x y : R), Rbar_lt a x -> x < y -> Rbar_lt y b -> f x < f y)).
Proof.
move => Df Hf x y Hax Hxy Hyb.
apply Rminus_lt_0.
case: (MVT_gen f x y df) => [z Hz | z Hz | c [Hc ->]].
apply Df.
apply Rbar_lt_le_trans with (y := Rmin x y) (2 := Rlt_le _ _ (proj1 Hz)).
rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
apply Rbar_le_lt_trans with (y := Rmax x y) (1 := Rlt_le _ _ (proj2 Hz)).
rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
apply derivable_continuous_pt.
exists (df z) ; apply is_derive_Reals, Df.
apply Rbar_lt_le_trans with (y := Rmin x y) (2 := proj1 Hz).
rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
apply Rbar_le_lt_trans with (y := Rmax x y) (1 := proj2 Hz).
rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
apply Rmult_lt_0_compat.
apply Hf.
apply Rbar_lt_le_trans with (y := Rmin x y) (2 := proj1 Hc).
rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
apply Rbar_le_lt_trans with (y := Rmax x y) (1 := proj2 Hc).
rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
Admitted.

Lemma incr_function_le (f : R -> R) (a b : Rbar) (df : R -> R) : (forall (x : R), Rbar_le a x -> Rbar_le x b -> is_derive f x (df x)) -> ((forall (x : R), Rbar_le a x -> Rbar_le x b -> df x > 0) -> (forall (x y : R), Rbar_le a x -> x < y -> Rbar_le y b -> f x < f y)).
Proof.
move => Df Hf x y Hax Hxy Hyb.
apply Rminus_lt_0.
case: (MVT_gen f x y df) => [z Hz | z Hz | c [Hc ->]].
apply Df.
apply Rbar_le_trans with (y := Rmin x y) (2 := Rlt_le _ _ (proj1 Hz)).
rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
apply Rbar_le_trans with (y := Rmax x y) (1 := Rlt_le _ _ (proj2 Hz)).
rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
apply derivable_continuous_pt.
exists (df z) ; apply is_derive_Reals, Df.
apply Rbar_le_trans with (y := Rmin x y) (2 := proj1 Hz).
rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
apply Rbar_le_trans with (y := Rmax x y) (1 := proj2 Hz).
rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
apply Rmult_lt_0_compat.
apply Hf.
apply Rbar_le_trans with (y := Rmin x y) (2 := proj1 Hc).
rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
apply Rbar_le_trans with (y := Rmax x y) (1 := proj2 Hc).
rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
Admitted.

Lemma MVT_cor4: forall (f df : R -> R) a eps, (forall c, Rabs (c - a) <= eps -> is_derive f c (df c)) -> forall b, (Rabs (b - a) <= eps) -> exists c, f b - f a = df c * (b - a) /\ (Rabs (c - a) <= Rabs (b - a)).
Proof.
intros f df a eps Hf' b.
unfold Rabs at 1 3.
case Rcase_abs; intros H1 H2.
destruct (MVT_cor2 f df b a).
rewrite -(Rplus_0_l a).
now apply Rlt_minus_l.
intros c Hc.
apply is_derive_Reals, Hf'.
rewrite Rabs_left1.
apply Rle_trans with (2:=H2).
apply Ropp_le_contravar.
now apply Rplus_le_compat_r.
apply Rplus_le_reg_r with a.
now ring_simplify.
exists x; split.
rewrite -RIneq.Ropp_minus_distr (proj1 H).
ring.
rewrite Rabs_left.
apply Ropp_le_contravar.
left; now apply Rplus_lt_compat_r.
apply Rplus_lt_reg_r with a.
now ring_simplify.
destruct H1.
destruct (MVT_cor2 f df a b).
apply Rplus_lt_reg_r with (-a).
ring_simplify.
now rewrite Rplus_comm.
intros c Hc.
apply is_derive_Reals, Hf'.
rewrite Rabs_right.
apply Rle_trans with (2:=H2).
now apply Rplus_le_compat_r.
apply Rle_ge; apply Rplus_le_reg_r with a.
now ring_simplify.
exists x; split.
exact (proj1 H0).
rewrite Rabs_right.
left; now apply Rplus_lt_compat_r.
apply Rle_ge; apply Rplus_le_reg_r with a.
left; now ring_simplify.
exists a.
replace b with a.
split;[ring|idtac].
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rle_refl.
apply Rplus_eq_reg_l with (-a).
ring_simplify.
Admitted.

Lemma bounded_variation (h dh : R -> R) (D : R) (x y : R) : (forall t : R, Rabs (t - x) <= Rabs (y - x) -> is_derive h t (dh t) /\ (Rabs (dh t) <= D)) -> Rabs (h y - h x) <= D * Rabs (y - x).
Proof.
intros H.
destruct (MVT_cor4 h dh x (Rabs (y - x))) with (b := y) as [t Ht].
intros c Hc.
specialize (H c Hc).
apply H.
apply Rle_refl.
rewrite (proj1 Ht).
rewrite Rabs_mult.
apply Rmult_le_compat_r.
apply Rabs_pos.
Admitted.

Lemma norm_le_prod_norm_1 {K : AbsRing} {U V : NormedModule K} (x : U * V) : norm (fst x) <= norm x.
Proof.
eapply Rle_trans, sqrt_plus_sqr.
rewrite Rabs_pos_eq.
apply Rmax_l.
Admitted.

Lemma is_derive_scal_l : forall (f : K -> K) (x l : K) (k : V), is_derive f x l -> is_derive (fun x => scal (f x) k) x (scal l k).
Proof.
intros f x l k Df.
eapply filterdiff_ext_lin.
apply @filterdiff_scal_l_fct ; try by apply locally_filter.
exact Df.
simpl => y.
apply sym_eq, scal_assoc.

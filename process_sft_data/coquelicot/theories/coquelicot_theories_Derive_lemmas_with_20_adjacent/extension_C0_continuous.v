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

Lemma norm_le_prod_norm_2 {K : AbsRing} {U V : NormedModule K} (x : U * V) : norm (snd x) <= norm x.
Proof.
eapply Rle_trans, sqrt_plus_sqr.
rewrite (Rabs_pos_eq (norm (snd x))).
apply Rmax_r.
Admitted.

Lemma is_derive_filterdiff (f : R -> R -> R) (x y : R) (dfx : R -> R -> R) (dfy : R) : locally (x,y) (fun u : R * R => is_derive (fun z => f z (snd u)) (fst u) (dfx (fst u) (snd u))) -> is_derive (fun z : R => f x z) y dfy -> continuous (fun u : R * R => dfx (fst u) (snd u)) (x,y) -> filterdiff (fun u : R * R => f (fst u) (snd u)) (locally (x,y)) (fun u : R * R => plus (scal (fst u) (dfx x y)) (scal (snd u) dfy)).
Proof.
intros Dx Dy Cx.
split.
apply (is_linear_comp (fun u : R * R => (scal (fst u) (dfx x y),scal (snd u) dfy)) (fun u : R * R => plus (fst u) (snd u))).
apply is_linear_prod.
apply (is_linear_comp (@fst _ _) (fun t : R => scal t (dfx x y))).
by apply is_linear_fst.
by apply @is_linear_scal_l.
apply (is_linear_comp (@snd _ _) (fun t : R => scal t dfy)).
by apply is_linear_snd.
by apply @is_linear_scal_l.
by apply @is_linear_plus.
simpl => u Hu.
replace u with (x,y) by now apply is_filter_lim_locally_unique.
move => {u Hu} eps /=.
set (eps' := pos_div_2 eps).
generalize (proj1 (filterlim_locally _ _) Cx eps') => {Cx} /= Cx.
generalize (filter_and _ _ Dx Cx) => {Dx Cx}.
intros (d1,Hd1).
destruct (proj2 Dy y (fun P H => H) eps') as (d2,Hd2).
set (l1 := dfx x y).
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)).
intros (u,v) (Hu,Hv) ; simpl in *.
set (g1 t := minus (f t v) (scal t l1)).
set (g2 t := minus (f x t) (scal t dfy)).
apply Rle_trans with (norm (minus (g1 u) (g1 x)) + norm (minus (g2 v) (g2 y))).
eapply Rle_trans, norm_triangle.
apply Req_le, f_equal, sym_eq.
rewrite /g1 /g2 /minus !opp_plus !opp_opp -!plus_assoc ; apply f_equal.
do 5 rewrite plus_comm -!plus_assoc ; apply f_equal.
rewrite !scal_distr_r !opp_plus -!plus_assoc !scal_opp_l !opp_opp.
rewrite plus_comm -!plus_assoc ; apply f_equal.
rewrite plus_comm -!plus_assoc ; apply f_equal.
by rewrite plus_comm -!plus_assoc plus_opp_l plus_zero_r.
replace (pos eps) with (eps' + eps') by (apply sym_eq ; apply double_var).
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
apply Rle_trans with (eps' * norm (minus u x)).
apply bounded_variation with (fun t => minus (dfx t v) l1) => t Ht.
split.
apply: is_derive_minus.
apply (Hd1 (t,v)) ; split ; simpl.
apply Rle_lt_trans with (1 := Ht).
apply Rlt_le_trans with (1:=Hu).
apply Rmin_l.
apply Rlt_le_trans with (1:=Hv).
apply Rmin_l.
rewrite -{2}(Rmult_1_r l1).
evar_last.
apply filterdiff_linear, is_linear_scal_l.
by rewrite Rmult_1_r.
apply Rlt_le.
apply (Hd1 (t,v)) ; split ; simpl.
apply Rle_lt_trans with (1 := Ht).
apply Rlt_le_trans with (1:=Hu).
apply Rmin_l.
apply Rlt_le_trans with (1:=Hv).
apply Rmin_l.
apply Rmult_le_compat_l.
apply Rlt_le.
apply cond_pos.
apply (norm_le_prod_norm_1 (minus (u, v) (x, y))).
apply Rle_trans with (eps' * norm (minus v y)).
apply Rle_trans with (norm (minus (minus (f x v) (f x y)) (scal (minus v y) dfy))).
right; apply f_equal.
rewrite /g2 scal_minus_distr_r /minus !opp_plus opp_opp -!plus_assoc ; apply f_equal.
rewrite plus_comm -!plus_assoc ; apply f_equal.
apply plus_comm.
apply Hd2.
apply Rlt_le_trans with (1:=Hv).
apply Rmin_r.
apply Rmult_le_compat_l.
apply Rlt_le.
apply cond_pos.
Admitted.

Lemma fn_eq_Derive_eq: forall f g a b, continuity_pt f a -> continuity_pt f b -> continuity_pt g a -> continuity_pt g b -> (forall x, a < x < b -> ex_derive f x) -> (forall x, a < x < b -> ex_derive g x) -> (forall x, a < x < b -> Derive f x = Derive g x) -> exists C, forall x, a <= x <= b -> f x = g x + C.
Proof.
intros f g a b Cfa Cfb Cga Cgb Df Dg Hfg.
pose (h := fun x => f x - g x).
assert (pr : forall x : R, a < x < b -> derivable_pt h x).
intros x Hx.
apply derivable_pt_minus.
eexists; apply is_derive_Reals, Derive_correct, Df, Hx.
eexists; apply is_derive_Reals, Derive_correct, Dg, Hx.
assert (constant_D_eq h (fun x : R => a <= x <= b) (h a)).
apply null_derivative_loc with (pr:=pr).
intros x Hx.
case (proj1 Hx).
case (proj2 Hx).
intros Y1 Y2.
apply derivable_continuous_pt.
apply pr; now split.
intros Y1 _; rewrite Y1.
apply continuity_pt_minus.
apply Cfb.
apply Cgb.
intros Y1; rewrite <- Y1.
apply continuity_pt_minus.
apply Cfa.
apply Cga.
intros x P.
apply trans_eq with (Derive h x).
apply sym_eq, is_derive_unique, is_derive_Reals.
now destruct (pr x P).
rewrite Derive_minus.
rewrite (Hfg _ P).
ring.
apply Df; split; apply P.
apply Dg; split; apply P.
unfold constant_D_eq in H.
exists (h a).
intros x Hx.
rewrite <- (H _ Hx).
Admitted.

Lemma extension_cont_continuous (f g : R -> U) (a : R) : continuous f a -> continuous g a -> f a = g a -> continuous (extension_cont f g a) a.
Proof.
simpl => Cf Cg Heq ; apply filterlim_locally => /= eps.
generalize (proj1 (filterlim_locally _ _) Cf eps) => {Cf} Cf.
generalize (proj1 (filterlim_locally _ _) Cg eps) => {Cg} Cg.
generalize (filter_and _ _ Cf Cg).
apply filter_imp => {Cf Cg} x [Cf Cg].
rewrite /extension_cont.
case: Rle_dec (Rle_refl a) => // _ _.
case: Rle_dec => // H.
Admitted.

Lemma extension_cont_is_derive (f g : R -> V) (a : R) (l : V) : is_derive f a l -> is_derive g a l -> f a = g a -> is_derive (extension_cont f g a) a l.
Proof.
case => _ Cf [_ Cg] Heq.
split.
by apply is_linear_scal_l.
move => x Hx eps.
move: (Cf x Hx eps) => {Cf} Cf.
move: (Cg x Hx eps) => {Cg} Cg.
generalize (is_filter_lim_locally_unique _ _ Hx) => {Hx} Hx.
rewrite -Hx {x Hx} in Cf, Cg |- *.
generalize (filter_and _ _ Cf Cg).
apply filter_imp => {Cf Cg} x [Cf Cg].
rewrite /extension_cont.
case: Rle_dec => Hx ; case: Rle_dec (Rle_refl a) => //= _ _.
Admitted.

Lemma extension_C0_ext (f : R -> V) (a b : Rbar) : forall (x : R), Rbar_le a x -> Rbar_le x b -> (extension_C0 f a b) x = f x.
Proof.
move => x Hax Hxb.
rewrite /extension_C0.
case: Rbar_le_dec => // _.
Admitted.

Lemma extension_C1_ext (f df : R -> V) (a b : Rbar) : forall (x : R), Rbar_le a x -> Rbar_le x b -> (extension_C1 f df a b) x = f x.
Proof.
move => x Hax Hxb.
rewrite /extension_C1.
case: Rbar_le_dec => // _.
Admitted.

Lemma extension_C1_is_derive (f df : R -> V) (a b : Rbar) : Rbar_le a b -> (forall x : R, Rbar_le a x -> Rbar_le x b -> is_derive f x (df x)) -> forall x : R, is_derive (extension_C1 f df a b) x (extension_C0 df a b x).
Proof.
intros Hab Cf x.
apply Rbar_le_lt_or_eq_dec in Hab ; case: Hab => Hab.
case: (Rbar_lt_le_dec x a) => Hax.
evar_last.
eapply is_derive_ext_loc.
apply locally_interval with m_infty a.
by [].
by [].
move => y _ Hay.
rewrite /extension_C1.
case: Rbar_le_dec => H.
contradict H ; by apply Rbar_lt_not_le.
reflexivity.
apply is_derive_plus.
apply is_derive_const.
apply @is_derive_scal_l.
apply @is_derive_minus.
apply is_derive_id.
apply is_derive_const.
rewrite plus_zero_l minus_zero_r scal_one.
rewrite /extension_C0.
case: Rbar_le_dec => H //.
by apply Rbar_le_not_lt in H.
apply Rbar_le_lt_or_eq_dec in Hax ; case: Hax => Hax.
case: (Rbar_lt_le_dec x b) => Hbx.
evar_last.
eapply is_derive_ext_loc.
apply locally_interval with a b.
by [].
by [].
move => y Hay Hby.
apply sym_eq, extension_C1_ext ; by apply Rbar_lt_le.
apply Cf ; by apply Rbar_lt_le.
rewrite /extension_C0.
case: Rbar_le_dec => // H.
case: Rbar_le_dec => // H0.
by apply Rbar_lt_le in Hbx.
by apply Rbar_lt_le in Hax.
apply Rbar_le_lt_or_eq_dec in Hbx ; case: Hbx => Hbx.
evar_last.
eapply is_derive_ext_loc.
apply locally_interval with b p_infty.
by [].
by [].
move => y Hby _.
rewrite /extension_C1.
case: Rbar_le_dec => H.
case: Rbar_le_dec => H0.
contradict H0 ; by apply Rbar_lt_not_le.
reflexivity.
contradict H ; eapply Rbar_le_trans, Rbar_lt_le, Hby.
by apply Rbar_lt_le.
apply is_derive_plus.
apply is_derive_const.
apply @is_derive_scal_l.
apply @is_derive_minus.
apply is_derive_id.
apply is_derive_const.
rewrite plus_zero_l minus_zero_r scal_one.
rewrite /extension_C0.
case: Rbar_le_dec => H //.
case: Rbar_le_dec => H0 //.
by apply Rbar_le_not_lt in H0.
by apply Rbar_lt_le in Hax.
destruct b as [b | | ] => //.
injection Hbx => {Hbx} Hbx.
rewrite -Hbx {x Hbx} in Hax |- *.
evar_last.
apply is_derive_ext_loc with (extension_cont f (fun x => plus (f (real b)) (scal (x - real b) (df (real b)))) b).
apply locally_interval with a p_infty => //.
move => y Hay _.
rewrite /extension_cont /extension_C1.
case: Rle_dec => H ; case: Rbar_le_dec => H0 ; case: (Rbar_le_dec y b) => // _.
contradict H0 ; by apply Rbar_lt_le.
contradict H0 ; by apply Rbar_lt_le.
apply extension_cont_is_derive => //.
apply Cf => /=.
by apply Rbar_lt_le.
by apply Rle_refl.
evar_last.
apply is_derive_plus.
apply is_derive_const.
apply @is_derive_scal_l.
apply @is_derive_minus.
apply is_derive_id.
apply is_derive_const.
by rewrite plus_zero_l minus_zero_r scal_one.
by rewrite Rminus_eq_0 @scal_zero_l plus_zero_r.
rewrite /extension_C0.
case: Rbar_le_dec => H0.
case: Rbar_le_dec (Rle_refl b) => //.
by apply Rbar_lt_le in Hax.
destruct a as [a | | ] => //.
injection Hax => {Hax} Hax.
rewrite -Hax {x Hax}.
evar_last.
apply is_derive_ext_loc with (extension_cont (fun x => plus (f (real a)) (scal (x - real a) (df (real a)))) f a).
apply locally_interval with m_infty b => //.
move => y _ Hbx.
rewrite /extension_cont /extension_C1.
case: Rle_dec => H ; case: Rbar_le_dec => //= H0 ; try case: Rbar_le_dec => // H1.
replace y with a by now apply Rle_antisym.
by rewrite Rminus_eq_0 @scal_zero_l plus_zero_r.
contradict H1 ; by apply Rbar_lt_le.
contradict H1 ; by apply Rbar_lt_le.
by contradict H0 ; apply Rlt_le, Rnot_le_lt.
apply extension_cont_is_derive => //.
apply is_derive_plus.
apply is_derive_const.
apply @is_derive_scal_l.
apply @is_derive_minus.
apply is_derive_id.
apply is_derive_const.
rewrite plus_zero_l minus_zero_r scal_one.
apply Cf.
by apply Rle_refl.
by apply Rbar_lt_le.
by rewrite Rminus_eq_0 @scal_zero_l plus_zero_r.
rewrite plus_zero_l minus_zero_r scal_one.
rewrite /extension_C0.
case: Rbar_le_dec (Rle_refl a) => // _ _.
case: Rbar_le_dec => H //.
by apply Rbar_lt_le in Hab.
rewrite -Hab {b Hab Cf}.
evar_last.
eapply is_derive_ext.
intros y.
rewrite /extension_C1.
case: Rbar_le_dec => H.
2: reflexivity.
case: Rbar_le_dec => // H0.
destruct a as [a | | ] => //.
replace y with a by now apply Rle_antisym.
by rewrite Rminus_eq_0 @scal_zero_l plus_zero_r.
apply is_derive_plus.
apply is_derive_const.
apply @is_derive_scal_l.
apply @is_derive_minus.
apply is_derive_id.
apply is_derive_const.
rewrite plus_zero_l minus_zero_r scal_one.
rewrite /extension_C0.
case: Rbar_le_dec => H //.
case: Rbar_le_dec => H0 //.
destruct a as [a | | ] => //.
Admitted.

Lemma extension_C1_ex_derive (f df : R -> R) (a b : Rbar) : Rbar_le a b -> (forall x : R, Rbar_le a x -> Rbar_le x b -> ex_derive f x) -> forall x : R, ex_derive (extension_C1 f (Derive f) a b) x.
Proof.
intros Hab Df x.
eexists.
apply extension_C1_is_derive => //.
intros y Hay Hby.
Admitted.

Lemma eq_is_derive : forall (f : R -> V) (a b : R), (forall t, a <= t <= b -> is_derive f t zero) -> a < b -> f a = f b.
Proof.
intros f a b Hd Hab.
apply ball_norm_eq => eps2.
pose eps := pos_div_2 eps2.
have Heps': 0 < eps / (b - a).
apply Rdiv_lt_0_compat.
apply eps.
exact: Rlt_Rminus.
pose eps' := mkposreal (eps / (b - a)) Heps'.
pose P t := norm (minus (f t) (f a)) <= eps' * (t - a).
pose A x := x <= b /\ forall t, a <= t <= x -> P t.
have H c : (forall t, a <= t < c -> P t) -> a <= c <= b -> exists delta:posreal, (forall t, a <= t <= Rmin b (c + delta) -> P t).
intros HP Hc.
destruct (Hd c Hc) as [_ Hd'].
refine (_ (Hd' c _ eps')).
case => delta H.
have Hdelta := cond_pos delta.
exists (pos_div_2 delta) => t Ht.
destruct (Rlt_le_dec t c) as [Htc|Htc].
apply HP.
now split.
unfold P.
replace (minus (f t) (f a)) with (plus (minus (f t) (f c)) (minus (f c) (f a))).
apply Rle_trans with (1 := norm_triangle _ _).
replace (eps' * (t - a)) with (eps' * (t - c) + eps' * (c - a)) by ring.
apply Rplus_le_compat.
move: (H t) => {H}.
rewrite scal_zero_r minus_zero_r -[norm (minus t c)]/(Rabs (t - c)).
rewrite -> Rabs_pos_eq by lra.
apply.
apply: norm_compat1.
change (Rabs (t - c) < delta).
apply Rabs_lt_between'.
cut (t <= c + delta/2).
lra.
apply Rle_trans with (1 := proj2 Ht).
apply Rmin_r.
set (d' := Rmax a (c - delta/2)).
replace (minus (f c) (f a)) with (plus (opp (minus (f d') (f c))) (minus (f d') (f a))).
apply Rle_trans with (1 := norm_triangle _ _).
replace (eps' * (c - a)) with (eps' * (c - d') + eps' * (d' - a)) by ring.
apply Rplus_le_compat.
move: (H d') => {H}.
rewrite scal_zero_r minus_zero_r -[norm (minus d' c)]/(Rabs (d' - c)).
rewrite norm_opp -Rabs_Ropp Rabs_pos_eq Ropp_minus_distr.
apply.
apply: norm_compat1.
change (Rabs (d' - c) < delta).
apply Rabs_lt_between'.
apply Rmax_case_strong ; lra.
apply Rmax_case_strong ; lra.
destruct (Req_dec a d') as [Had|Had].
rewrite Had.
rewrite /minus plus_opp_r /Rminus Rplus_opp_r Rmult_0_r norm_zero.
apply Rle_refl.
apply HP.
revert Had.
apply Rmax_case_strong ; lra.
by rewrite opp_minus /minus plus_assoc -(plus_assoc (f c)) plus_opp_l plus_zero_r.
by rewrite /minus plus_assoc -(plus_assoc (f t)) plus_opp_l plus_zero_r.
easy.
assert (Ha : A a).
apply (conj (Rlt_le _ _ Hab)).
intros t [Ht1 Ht2].
rewrite (Rle_antisym _ _ Ht2 Ht1).
rewrite /P /minus plus_opp_r /Rminus Rplus_opp_r Rmult_0_r norm_zero.
apply Rle_refl.
destruct (completeness A) as [s [Hs1 Hs2]].
now exists b => t [At _].
now exists a.
assert (Hs: forall t, a <= t < s -> P t).
intros t Ht.
apply Rnot_lt_le => H'.
specialize (Hs2 t).
apply (Rlt_not_le _ _ (proj2 Ht)), Hs2.
intros x [Ax1 Ax2].
apply Rnot_lt_le => Hxt.
apply (Rlt_not_le _ _ H').
apply Ax2.
lra.
destruct (Req_dec s b) as [->|Hsb].
-
destruct (H b) as [delta Hdelta].
apply Hs.
lra.
apply Rle_lt_trans with (eps' * (b - a)).
apply: Hdelta.
have Hdelta := cond_pos delta.
rewrite Rmin_left ; lra.
simpl.
have Heps2 := cond_pos eps2.
field_simplify ; lra.
-
destruct (H s) as [delta Hdelta].
apply Hs.
split.
now apply Hs1.
apply Hs2.
intros x.
by case.
eelim Rle_not_lt.
apply Hs1.
split.
apply Rmin_l.
apply Hdelta.
apply Rmin_case.
destruct (Hs2 b) ; try easy.
intros x.
by case.
have Hdelta' := cond_pos delta.
Admitted.

Lemma is_derive_n_unique f n x l : is_derive_n f n x l -> Derive_n f n x = l.
Proof.
case n.
easy.
simpl; intros n0 H.
Admitted.

Lemma Derive_n_correct f n x : ex_derive_n f n x -> is_derive_n f n x (Derive_n f n x).
Proof.
case: n => /= [ | n] Hf.
by [].
Admitted.

Lemma Derive_n_ext_loc : forall f g n x, locally x (fun t => f t = g t) -> Derive_n f n x = Derive_n g n x.
Proof.
intros f g n x Heq.
pattern x ; apply locally_singleton.
induction n.
exact Heq.
apply locally_locally in IHn.
apply filter_imp with (2 := IHn) => {IHn}.
intros t H.
Admitted.

Lemma ex_derive_n_ext_loc : forall f g n x, locally x (fun t => f t = g t) -> ex_derive_n f n x -> ex_derive_n g n x.
Proof.
intros f g n x Heq.
case: n => /= [ | n].
by [].
apply ex_derive_ext_loc.
apply locally_locally in Heq.
apply filter_imp with (2 := Heq) => {Heq}.
Admitted.

Lemma is_derive_n_ext_loc : forall f g n x l, locally x (fun t => f t = g t) -> is_derive_n f n x l -> is_derive_n g n x l.
Proof.
intros f g n x l Heq.
case: n => /= [ | n].
move => <- ; apply sym_eq.
pattern x ; now apply locally_singleton.
apply is_derive_ext_loc.
apply locally_locally in Heq.
apply filter_imp with (2 := Heq) => {Heq}.
Admitted.

Lemma Derive_n_ext : forall f g n x, (forall t, f t = g t) -> Derive_n f n x = Derive_n g n x.
Proof.
intros f g n x Heq.
apply Derive_n_ext_loc.
Admitted.

Lemma ex_derive_n_ext : forall f g n x, (forall t, f t = g t) -> ex_derive_n f n x -> ex_derive_n g n x.
Proof.
intros f g n x Heq.
apply ex_derive_n_ext_loc.
Admitted.

Lemma is_derive_n_ext : forall f g n x l, (forall t, f t = g t) -> is_derive_n f n x l -> is_derive_n g n x l.
Proof.
intros f g n x l Heq.
apply is_derive_n_ext_loc.
Admitted.

Lemma Derive_n_comp: forall f n m x, Derive_n (Derive_n f m) n x = Derive_n f (n+m) x.
Proof.
intros f n m.
induction n.
now simpl.
simpl.
intros x.
Admitted.

Lemma is_derive_Sn (f : R -> R) (n : nat) (x l : R) : locally x (ex_derive f) -> (is_derive_n f (S n) x l <-> is_derive_n (Derive f) n x l).
Proof.
move => Hf.
case: n => /= [ | n].
split => H.
by apply is_derive_unique.
rewrite -H ; apply Derive_correct.
now apply locally_singleton.
split => Hf'.
-
apply is_derive_ext with (2 := Hf').
move => y ; rewrite (Derive_n_comp _ n 1%nat).
by (replace (n + 1)%nat with (S n) by ring).
-
apply is_derive_ext with (2 := Hf').
move => y ; rewrite (Derive_n_comp _ n 1%nat).
Admitted.

Lemma is_derive_n_const n a : forall x, is_derive_n (fun _ => a) (S n) x 0.
Proof.
elim: n => /= [ | n IH] x.
by apply @is_derive_const.
eapply is_derive_ext.
intros t ; apply sym_equal, is_derive_unique, IH.
Admitted.

Lemma ex_derive_n_const a n x: ex_derive_n (fun _ => a) n x.
Proof.
case: n => //= ; case => //= [ | n].
apply ex_derive_const.
eapply ex_derive_ext.
intros t ; apply sym_equal, is_derive_unique, is_derive_n_const.
Admitted.

Lemma Derive_n_const n a : forall x, Derive_n (fun _ => a) (S n) x = 0.
Proof.
Admitted.

Lemma Derive_n_opp (f : R -> R) (n : nat) (x : R) : Derive_n (fun x => - f x) n x = - Derive_n f n x.
Proof.
elim: n x => [ | n IH] x /=.
by [].
rewrite -Derive_opp.
Admitted.

Lemma ex_derive_n_opp (f : R -> R) (n : nat) (x : R) : ex_derive_n f n x -> ex_derive_n (fun x => -f x) n x.
Proof.
case: n x => [ | n] /= x Hf.
by [].
apply ex_derive_opp in Hf.
apply: ex_derive_ext Hf.
Admitted.

Lemma is_derive_n_opp (f : R -> R) (n : nat) (x l : R) : is_derive_n f n x l -> is_derive_n (fun x => -f x) n x (- l).
Proof.
case: n x => [ | n] /= x Hf.
by rewrite Hf.
apply is_derive_opp in Hf.
apply: is_derive_ext Hf.
Admitted.

Lemma extension_C0_continuous (f : R -> V) (a b : Rbar) : Rbar_le a b -> (forall x : R, Rbar_le a x -> Rbar_le x b -> continuous f x) -> forall x, continuous (extension_C0 f a b) x.
Proof.
intros Hab Cf x.
apply Rbar_le_lt_or_eq_dec in Hab ; case: Hab => Hab.
case: (Rbar_lt_le_dec x a) => Hax.
eapply continuous_ext_loc.
apply locally_interval with m_infty a.
by [].
by [].
move => y _ Hay.
rewrite /extension_C0.
case: Rbar_le_dec => H.
contradict H ; by apply Rbar_lt_not_le.
reflexivity.
apply continuous_const.
apply Rbar_le_lt_or_eq_dec in Hax ; case: Hax => Hax.
case: (Rbar_lt_le_dec x b) => Hbx.
eapply continuous_ext_loc.
apply locally_interval with a b.
by [].
by [].
move => y Hay Hby.
rewrite /extension_C0.
case: Rbar_le_dec => H.
case: Rbar_le_dec => H0.
reflexivity.
contradict H0 ; by apply Rbar_lt_le.
contradict H ; by apply Rbar_lt_le.
apply Cf ; by apply Rbar_lt_le.
apply Rbar_le_lt_or_eq_dec in Hbx ; case: Hbx => Hbx.
eapply continuous_ext_loc.
apply locally_interval with b p_infty.
by [].
by [].
move => y Hby _.
rewrite /extension_C0.
case: Rbar_le_dec => H.
case: Rbar_le_dec => H0.
contradict H0 ; by apply Rbar_lt_not_le.
reflexivity.
contradict H ; eapply Rbar_le_trans, Rbar_lt_le, Hby.
by apply Rbar_lt_le.
apply continuous_const.
destruct b as [b | | ] => //.
injection Hbx => {Hbx} Hbx.
rewrite -Hbx {x Hbx} in Hax |- *.
apply continuous_ext_loc with (extension_cont f (fun _ => f (real b)) b).
apply locally_interval with a p_infty => //.
move => y Hay _.
rewrite /extension_cont /extension_C0.
case: Rle_dec => H ; case: Rbar_le_dec => H0 ; case: (Rbar_le_dec y b) => // _.
contradict H0 ; by apply Rbar_lt_le.
contradict H0 ; by apply Rbar_lt_le.
apply extension_cont_continuous => //.
apply Cf => /=.
by apply Rbar_lt_le.
by apply Rle_refl.
by apply continuous_const.
destruct a as [a | | ] => //.
injection Hax => {Hax} Hax.
rewrite -Hax {x Hax}.
apply continuous_ext_loc with (extension_cont (fun _ => f (real a)) f a).
apply locally_interval with m_infty b => //.
move => y _ Hbx.
rewrite /extension_cont /extension_C0.
case: Rle_dec => H ; case: Rbar_le_dec => //= H0 ; try case: Rbar_le_dec => // H1.
by replace y with a by now apply Rle_antisym.
contradict H1 ; by apply Rbar_lt_le.
contradict H1 ; by apply Rbar_lt_le.
by contradict H0 ; apply Rlt_le, Rnot_le_lt.
apply extension_cont_continuous => //.
by apply continuous_const.
apply Cf.
by apply Rle_refl.
by apply Rbar_lt_le.
rewrite -Hab {b Hab Cf}.
eapply continuous_ext.
intros y.
rewrite /extension_C0.
case: Rbar_le_dec => H.
2: reflexivity.
case: Rbar_le_dec => // H0.
destruct a as [a | | ] => //.
by replace y with a by now apply Rle_antisym.
by apply continuous_const.

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

Lemma is_domin_linear {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> W) (g : T -> U) (l : U -> V) : is_linear l -> is_domin F f g -> is_domin F f (fun t => l (g t)).
Proof.
intros [_ _ [M [Hm Hn]]] H eps.
assert (He : 0 < eps / M).
apply Rdiv_lt_0_compat with (2 := Hm).
apply cond_pos.
specialize (H (mkposreal _ He)).
move: H ; apply filter_imp => /= x Hx.
apply Rle_trans with (1 := Hn _).
evar_last.
apply Rmult_le_compat_l with (2 := Hx).
now apply Rlt_le.
field.
Admitted.

Lemma filterdiff_continuous_aux {F} {FF : Filter F} (f : U -> V) : ex_filterdiff f F -> forall x, is_filter_lim F x -> filterlim f F (locally (f x)).
Proof.
intros [l [Hl Df]] x Hx.
specialize (Df x Hx).
apply filterlim_locally_ball_norm => eps.
specialize (Df (mkposreal _ Rlt_0_1)) ; simpl in Df.
destruct (linear_norm _ Hl) as [M Hm].
assert (F (fun y => norm (minus (f y) (f x)) <= (M + 1) * norm (minus y x))).
move: Df ; apply filter_imp => y Hy.
rewrite Rmult_1_l in Hy.
apply Rle_trans with (1 := norm_triangle_inv _ _) in Hy.
apply Rabs_le_between' in Hy.
eapply Rle_trans.
by apply Hy.
apply Rle_minus_r ; ring_simplify.
by apply Hm.
move: H => {Df} Df.
assert (Hm': 0 < M + 1).
apply Rplus_le_lt_0_compat.
apply Rlt_le, Hm.
exact Rlt_0_1.
assert (0 < eps / (M+1)).
apply Rdiv_lt_0_compat with (2 := Hm').
apply cond_pos.
specialize (Hx _ (locally_ball_norm x (mkposreal _ H))).
generalize (filter_and _ _ Hx Df) => /=.
apply filter_imp => y [Hy Hy'] {Hx Df}.
apply Rle_lt_trans with (1 := Hy').
evar_last.
now apply Rmult_lt_compat_l with (2 := Hy).
field.
Admitted.

Lemma filterdiff_continuous (f : U -> V) x : ex_filterdiff f (locally x) -> continuous f x.
Proof.
intros.
Admitted.

Lemma filterdiff_locally {F} {FF : ProperFilter F} (f : U -> V) x l : is_filter_lim F x -> filterdiff f (locally x) l -> filterdiff f F l.
Proof.
intros Fx [Hl Df].
split.
exact Hl.
intros z Fz.
specialize (Df _ (fun P H => H)).
generalize (is_filter_lim_unique _ _ Fx Fz).
intros ->.
Admitted.

Lemma ex_filterdiff_locally {F} {FF : ProperFilter F} (f : U -> V) x : is_filter_lim F x -> ex_filterdiff f (locally x) -> ex_filterdiff f F.
Proof.
intros Fx [l Df].
eexists.
apply filterdiff_locally with x.
by [].
Admitted.

Lemma filterdiff_ext_lin {F} {FF : Filter F} (f : U -> V) (l1 l2 : U -> V) : filterdiff f F l1 -> (forall y, l1 y = l2 y) -> filterdiff f F l2.
Proof.
intros [Hl1 Hf1] Hl ; split => [ | x Hx eps].
+
split.
-
intros x y ; rewrite -!Hl.
by apply linear_plus.
-
intros k x ; rewrite -!Hl.
by apply linear_scal.
-
destruct (linear_norm _ Hl1) as [M Hm].
exists M ; split.
by apply Hm.
move => x ; now rewrite -Hl.
+
move: (Hf1 x Hx eps).
apply filter_imp => y.
Admitted.

Lemma filterdiff_ext_loc {F} {FF : Filter F} (f g : U -> V) (l : U -> V) : F (fun y => f y = g y) -> (forall x, is_filter_lim F x -> f x = g x) -> filterdiff f F l -> filterdiff g F l.
Proof.
move => H H0 [Hl Df].
split => //.
move => x Hx eps.
specialize (H0 x Hx).
specialize (Df x Hx eps).
apply filter_and with (1 := H) in Df.
move: Df ; apply filter_imp => y [Hy].
apply Rle_trans.
Admitted.

Lemma ex_filterdiff_ext_loc {F} {FF : Filter F} (f g : U -> V) : F (fun y => f y = g y) -> (forall x, is_filter_lim F x -> f x = g x) -> ex_filterdiff f F -> ex_filterdiff g F.
Proof.
intros H H0 [l Hl].
Admitted.

Lemma filterdiff_ext_locally (f g : U -> V) (x : U) (l : U -> V) : locally x (fun y => f y = g y) -> filterdiff f (locally x) l -> filterdiff g (locally x) l.
Proof.
move => H.
apply filterdiff_ext_loc with (1 := H).
move => y Hy.
destruct H as [d Hd].
apply Hd.
replace y with x.
apply ball_center.
Admitted.

Lemma ex_filterdiff_ext_locally (f g : U -> V) x : locally x (fun y => f y = g y) -> ex_filterdiff f (locally x) -> ex_filterdiff g (locally x).
Proof.
intros H [l Hl].
Admitted.

Lemma ex_filterdiff_ext {F} {FF : Filter F} (f g : U -> V) : (forall y , f y = g y) -> ex_filterdiff f F -> ex_filterdiff g F.
Proof.
intros H [l Hl].
Admitted.

Lemma filterdiff_const {F} {FF : Filter F} (a : V) : filterdiff (fun _ => a) F (fun _ => zero).
Proof.
split.
by apply is_linear_zero.
move => x Hx eps.
apply filter_imp with (2 := filter_true) => y _.
rewrite /minus plus_opp_r plus_zero_l norm_opp norm_zero.
apply Rmult_le_pos.
by apply Rlt_le, eps.
Admitted.

Lemma ex_filterdiff_const {F} {FF : Filter F} (a : V) : ex_filterdiff (fun _ => a) F.
Proof.
intros.
exists (fun _ => zero).
Admitted.

Lemma filterdiff_linear {F} (l : U -> V) : is_linear l -> filterdiff l F l.
Proof.
move => Hl ; split.
by [].
move => x Hx eps.
apply Hx.
apply filter_forall => y.
rewrite /minus -(linear_opp l x Hl) -linear_plus // plus_opp_r norm_zero.
apply Rmult_le_pos.
apply Rlt_le, eps.
Admitted.

Lemma ex_filterdiff_linear {F} (l : U -> V) : is_linear l -> ex_filterdiff l F.
Proof.
Admitted.

Lemma filterdiff_comp {F} {FF : Filter F} f g (lf : U -> V) (lg : V -> W) : filterdiff f F lf -> filterdiff g (filtermap f F) lg -> filterdiff (fun y => g (f y)) F (fun y => lg (lf y)).
Proof.
intros Df Dg.
split.
apply is_linear_comp.
by apply Df.
by apply Dg.
intros x Hx.
assert (Cf : filterlim f F (locally (f x))).
apply filterdiff_continuous_aux with (2 := Hx).
eexists ; by apply Df.
assert (is_domin (filtermap f F) (fun y : V => minus y (f x)) (fun y : V => minus (minus (g y) (g (f x))) (lg (minus y (f x))))).
apply Dg.
move => P HP.
by apply Cf.
destruct Dg as [Hg _].
rename H into Dg.
destruct Df as [Hf Df].
apply domin_rw_r with (fun y : U => plus (minus (minus (g (f y)) (g (f x))) (lg (minus (f y) (f x)))) (lg (minus (minus (f y) (f x)) (lf (minus y x))))).
apply equiv_ext_loc.
apply filter_forall => y.
rewrite /minus -!plus_assoc.
repeat apply f_equal.
rewrite plus_assoc.
rewrite (linear_plus _ Hg (plus _ _)).
rewrite plus_assoc.
rewrite plus_opp_l plus_zero_l.
by apply linear_opp.
apply domin_plus.
intros eps.
destruct (linear_norm _ Hf) as [mf [Hmf Hnf]].
assert (F (fun y => norm (minus (f y) (f x)) <= (1 + mf) * norm (minus y x))).
specialize (Df x Hx (mkposreal _ Rlt_0_1)).
move: Df ; apply filter_imp.
move => y /= Hy.
replace (minus (f y) (f x)) with (plus (minus (minus (f y) (f x)) (lf (minus y x))) (lf (minus y x))).
eapply Rle_trans.
apply @norm_triangle.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
exact Hy.
by apply Hnf.
by rewrite {1}/minus -plus_assoc plus_opp_l plus_zero_r.
clear Df ; rename H into Df.
assert (He : 0 < eps / (1 + mf)).
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rplus_lt_0_compat.
exact Rlt_0_1.
exact Hmf.
specialize (Dg (mkposreal _ He)).
unfold filtermap in Dg.
generalize (filter_and _ _ Df Dg).
apply filter_imp => /= y {Df Dg} [Df Dg].
apply Rle_trans with (1 := Dg).
unfold Rdiv.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le, eps.
rewrite Rmult_comm ; apply Rle_div_l.
apply Rplus_lt_0_compat.
exact Rlt_0_1.
exact Hmf.
rewrite Rmult_comm ; by apply Df.
specialize (Df x Hx).
Admitted.

Lemma ex_filterdiff_comp {F} {FF : Filter F} (f : U -> V) (g : V -> W) : ex_filterdiff f F -> ex_filterdiff g (filtermap f F) -> ex_filterdiff (fun y => g (f y)) F.
Proof.
intros [lf Df] [lg Dg].
Admitted.

Lemma filterdiff_comp' f g x (lf : U -> V) (lg : V -> W) : filterdiff f (locally x) lf -> filterdiff g (locally (f x)) lg -> filterdiff (fun y => g (f y)) (locally x) (fun y => lg (lf y)).
Proof.
intros.
apply filterdiff_comp.
by [].
apply filterdiff_locally with (f x).
apply is_filter_lim_filtermap => //.
apply filterdiff_continuous => //.
eexists ; by apply H.
Admitted.

Lemma ex_filterdiff_comp' (f : U -> V) (g : V -> W) x : ex_filterdiff f (locally x) -> ex_filterdiff g (locally (f x)) -> ex_filterdiff (fun y => g (f y)) (locally x).
Proof.
intros [lf Df] [lg Dg].
eexists.
Admitted.

Lemma filterdiff_comp_2 {F : (T -> Prop) -> Prop} {FF : Filter F} : forall (f : T -> U) (g : T -> V) (h : U -> V -> W) (lf : T -> U) (lg : T -> V) (lh : U -> V -> W), filterdiff f F lf -> filterdiff g F lg -> filterdiff (fun t => h (fst t) (snd t)) (filtermap (fun t => (f t,g t)) F) (fun t => lh (fst t) (snd t)) -> filterdiff (fun y : T => h (f y) (g y)) F (fun y : T => lh (lf y) (lg y)).
Proof.
intros f g h lf lg lh [Hf Df] [Hg Dg] Dh.
apply (filterdiff_comp (fun t => (f t, g t)) _ (fun t => (lf t, lg t)) _) in Dh.
by [].
split.
by apply is_linear_prod.
intros x Hx eps.
assert (0 < eps / sqrt 2).
apply Rdiv_lt_0_compat.
by apply eps.
apply Rlt_sqrt2_0.
generalize (filter_and _ _ (Df x Hx (mkposreal _ H)) (Dg x Hx (mkposreal _ H))).
simpl pos.
apply filter_imp ; intros y [Hnf Hng].
eapply Rle_trans.
apply norm_prod.
simpl fst ; simpl snd.
eapply Rle_trans.
apply Rmult_le_compat_l.
by apply sqrt_pos.
apply Rmax_case.
apply Hnf.
apply Hng.
apply Req_le ; field.
Admitted.

Lemma filterdiff_ext {F} {FF : Filter F} (f g : U -> V) (l : U -> V) : (forall y , f y = g y) -> filterdiff f F l -> filterdiff g F l.
Proof.
move => H.
apply filterdiff_ext_loc => //.
now apply filter_imp with (2 := filter_true).

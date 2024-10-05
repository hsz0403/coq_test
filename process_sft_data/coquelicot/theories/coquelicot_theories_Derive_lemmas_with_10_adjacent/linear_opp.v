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

Lemma linear_zero (l : U -> V) : is_linear l -> l zero = zero.
Proof.
intros Hl.
rewrite -(scal_zero_l zero).
rewrite linear_scal.
exact (scal_zero_l (l zero)).
Admitted.

Lemma linear_cont (l : U -> V) (x : U) : is_linear l -> continuous l x.
Proof.
intros Hl.
apply filterlim_locally_ball_norm => eps.
apply locally_le_locally_norm.
case: (linear_norm _ Hl) => M Hn.
assert (0 < eps / M).
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Hn.
exists (mkposreal _ H) => y Hy.
rewrite /ball_norm /minus -linear_opp // -linear_plus //.
eapply Rle_lt_trans.
by apply Hn.
evar_last.
apply Rmult_lt_compat_l with (2 := Hy).
apply Hn.
simpl.
field.
Admitted.

Lemma is_linear_ext (l1 l2 : U -> V) : (forall x, l1 x = l2 x) -> is_linear l1 -> is_linear l2.
Proof.
intros Hl Hl1.
split.
intros ; rewrite -!Hl ; apply Hl1.
intros ; rewrite -!Hl ; apply Hl1.
case: Hl1 => _ _ [M Hl1].
exists M ; split.
by apply Hl1.
Admitted.

Lemma is_linear_zero : is_linear (fun _ => zero).
Proof.
repeat split.
-
move => _ _ ; by rewrite plus_zero_l.
-
move => k _ ; by rewrite scal_zero_r.
-
exists 1 ; split.
exact Rlt_0_1.
move => x ; rewrite Rmult_1_l norm_zero.
Admitted.

Lemma is_linear_comp {K : AbsRing} {U V W : NormedModule K} (l1 : U -> V) (l2 : V -> W) : is_linear l1 -> is_linear l2 -> is_linear (fun x => l2 (l1 x)).
Proof.
intros Hl1 Hl2.
split.
-
move => x y.
by rewrite !linear_plus.
-
move => k x.
by rewrite !linear_scal.
-
destruct (linear_norm _ Hl1) as [M1 Hn1].
destruct (linear_norm _ Hl2) as [M2 Hn2].
exists (M2 * M1) ; split.
now apply Rmult_lt_0_compat.
move => x.
eapply Rle_trans.
by apply Hn2.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
now apply Rlt_le.
Admitted.

Lemma is_linear_id : is_linear (fun (x : V) => x).
Proof.
repeat split.
-
exists 1 ; split.
exact Rlt_0_1.
move => x ; rewrite Rmult_1_l.
Admitted.

Lemma is_linear_opp : is_linear (@opp V).
Proof.
repeat split.
-
move => x y.
now apply opp_plus.
-
move => k x.
apply sym_eq.
apply: scal_opp_r.
-
exists 1 ; split.
exact Rlt_0_1.
move => x ; rewrite norm_opp Rmult_1_l.
Admitted.

Lemma is_linear_plus : is_linear (fun x : V * V => plus (fst x) (snd x)).
Proof.
repeat split.
-
move => x y.
rewrite -!plus_assoc ; apply f_equal.
rewrite plus_comm -!plus_assoc.
by apply f_equal, @plus_comm.
-
move => k x.
now rewrite scal_distr_l.
-
exists 2 ; split.
exact Rlt_0_2.
move => x /= ; eapply Rle_trans.
by apply @norm_triangle.
rewrite Rmult_plus_distr_r Rmult_1_l ; apply Rplus_le_compat.
apply Rle_trans with (2 := proj1 (sqrt_plus_sqr _ _)).
rewrite -> Rabs_pos_eq by apply norm_ge_0.
by apply Rmax_l.
apply Rle_trans with (2 := proj1 (sqrt_plus_sqr _ _)).
rewrite -> (Rabs_pos_eq (norm (snd x))) by apply norm_ge_0.
Admitted.

Lemma is_linear_scal_l (x : V) : is_linear (fun k : K => scal k x).
Proof.
split.
-
move => u v ; by apply @scal_distr_r.
-
move => u v /= ; apply sym_eq, @scal_assoc.
-
exists (norm x + 1) ; split.
apply Rplus_le_lt_0_compat.
apply norm_ge_0.
exact Rlt_0_1.
move => k /=.
rewrite Rmult_plus_distr_r Rmult_1_l -(Rplus_0_r (norm (scal k x))).
apply Rplus_le_compat.
now rewrite Rmult_comm ; apply norm_scal.
Admitted.

Lemma is_linear_scal_r (k : K) : (forall n m : K, mult n m = mult m n) -> is_linear (fun x : V => scal k x).
Proof.
split.
-
move => u v ; by apply @scal_distr_l.
-
move => u v /= ; apply sym_eq ; rewrite !@scal_assoc.
by rewrite H.
-
exists (abs k + 1) ; split.
apply Rplus_le_lt_0_compat.
apply abs_ge_0.
exact Rlt_0_1.
move => x /=.
rewrite Rmult_plus_distr_r Rmult_1_l -(Rplus_0_r (norm (scal k x))).
apply Rplus_le_compat.
apply norm_scal.
Admitted.

Lemma is_linear_prod {K : AbsRing} {T U V : NormedModule K} (l1 : T -> U) (l2 : T -> V) : is_linear l1 -> is_linear l2 -> is_linear (fun t : T => (l1 t, l2 t)).
Proof.
intros H1 H2.
split.
-
intros x y.
apply injective_projections ; simpl.
by apply H1.
by apply H2.
-
intros k x.
apply injective_projections ; simpl.
by apply H1.
by apply H2.
-
destruct (linear_norm l1 H1) as [M1 [HM1 Hn1]].
destruct (linear_norm l2 H2) as [M2 [HM2 Hn2]].
exists (sqrt 2 * Rmax M1 M2)%R ; split.
apply Rmult_lt_0_compat.
apply sqrt_lt_R0, Rlt_0_2.
by apply Rmax_case.
intros x.
eapply Rle_trans.
apply norm_prod.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
by apply sqrt_pos.
rewrite Rmult_max_distr_r.
apply Rmax_case.
by eapply Rle_trans, Rmax_l.
by eapply Rle_trans, Rmax_r.
Admitted.

Lemma linear_opp (l : U -> V) (x : U) : is_linear l -> l (opp x) = opp (l x).
Proof.
intros Hl.
apply plus_reg_r with (l x).
rewrite <- linear_plus, !plus_opp_l.
by apply linear_zero.
exact Hl.

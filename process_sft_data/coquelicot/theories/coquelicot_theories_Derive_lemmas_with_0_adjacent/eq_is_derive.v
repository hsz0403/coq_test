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
lra.

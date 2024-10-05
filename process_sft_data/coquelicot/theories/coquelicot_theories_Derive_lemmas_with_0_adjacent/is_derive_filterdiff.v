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
apply (norm_le_prod_norm_2 (minus (u, v) (x, y))).

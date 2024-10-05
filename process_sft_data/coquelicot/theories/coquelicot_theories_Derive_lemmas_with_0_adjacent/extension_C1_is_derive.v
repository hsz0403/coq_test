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
by replace a with x by now apply Rle_antisym.

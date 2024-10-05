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

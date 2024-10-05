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

Lemma is_derive_scal_l : forall (f : K -> K) (x l : K) (k : V), is_derive f x l -> is_derive (fun x => scal (f x) k) x (scal l k).
Proof.
intros f x l k Df.
eapply filterdiff_ext_lin.
apply @filterdiff_scal_l_fct ; try by apply locally_filter.
exact Df.
simpl => y.
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

Lemma is_derive_mult : forall (f g : R -> R) (x : R) (df dg : R), is_derive f x df -> is_derive g x dg -> is_derive (fun t : R => f t * g t) x (df * g x + f x * dg) .
Proof.
intros f g x df dg Df Dg.
eapply filterdiff_ext_lin.
apply @filterdiff_mult_fct with (2 := Df) (3 := Dg).
exact Rmult_comm.
rewrite /scal /= /mult /plus /= => y.
ring.

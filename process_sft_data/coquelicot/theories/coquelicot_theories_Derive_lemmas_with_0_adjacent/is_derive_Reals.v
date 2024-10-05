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

Lemma is_derive_Reals (f : R -> R) (x l : R) : is_derive f x l <-> derivable_pt_lim f x l.
Proof.
apply iff_sym.
split => Hf.
+
split.
apply @is_linear_scal_l.
simpl => y Hy eps.
rewrite -(is_filter_lim_locally_unique _ _ Hy) ; clear y Hy.
case: (Hf eps (cond_pos _)) => {Hf} d Hf.
exists d => y /= Hy.
case: (Req_dec y x) => Hxy.
rewrite Hxy /norm /scal /= /abs /minus /plus /opp /mult /=.
ring_simplify (f x + - f x + - ((x + - x) * l)).
ring_simplify (x + - x).
rewrite Rabs_R0 Rmult_0_r.
by apply Rle_refl.
apply Rle_div_l.
apply Rabs_pos_lt.
by apply Rminus_eq_contra.
rewrite -Rabs_div.
2: by apply Rminus_eq_contra.
rewrite /scal /= /minus /plus /opp /mult /=.
replace ((f y + - f x + - ((y + - x) * l)) / (y + - x)) with ((f (x + (y-x)) - f x) / (y-x) - l).
2: ring_simplify (x + (y - x)) ; field ; by apply Rminus_eq_contra.
apply Rlt_le, Hf.
by apply Rminus_eq_contra.
by [].
+
move => e He.
destruct Hf as [_ Hf].
specialize (Hf x (fun P H => H)).
destruct (Hf (pos_div_2 (mkposreal _ He))) as [delta Hd].
exists delta => h Hh0 Hh.
apply Rle_lt_trans with (e / 2).
simpl in Hd.
replace ((f (x + h) - f x) / h - l) with ((f (x + h) + - f x + - ((x + h + - x) * l)) / (x + h + - x)).
2: by field.
rewrite Rabs_div.
2: by ring_simplify (x + h + - x).
apply Rle_div_l.
now ring_simplify (x + h + - x) ; apply Rabs_pos_lt.
apply Hd.
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /=.
by ring_simplify (x + h + - x).
apply Rlt_div_l, Rminus_lt_0 ; ring_simplify.
by apply Rlt_0_2.
by [].

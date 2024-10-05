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

Lemma Derive_ext_loc : forall f g x, locally x (fun t => f t = g t) -> Derive f x = Derive g x.
Proof.
intros f g x Hfg.
rewrite /Derive /Lim.
apply f_equal, Lim_seq_ext_loc.
apply (filterlim_Rbar_loc_seq 0 (fun h => (f (x + h) - f x) / h = (g (x + h) - g x) / h)).
apply (filter_imp (fun h => f (x + h) = g (x + h))).
intros h ->.
by rewrite (locally_singleton _ _ Hfg).
destruct Hfg as [eps He].
exists eps => h H Hh.
apply He.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /=.
Admitted.

Lemma Derive_ext : forall f g x, (forall t, f t = g t) -> Derive f x = Derive g x.
Proof.
intros f g x Hfg.
apply Derive_ext_loc.
Admitted.

Lemma is_derive_const : forall (a : V) (x : K), is_derive (fun _ : K => a) x zero.
Proof.
intros a x.
apply filterdiff_ext_lin with (fun y : K => zero).
apply filterdiff_const.
intros y.
apply sym_eq.
Admitted.

Lemma ex_derive_const : forall (a : V) (x : K), ex_derive (fun _ => a) x.
Proof.
intros a x.
eexists.
Admitted.

Lemma Derive_const : forall (a x : R), Derive (fun _ => a) x = 0.
Proof.
intros a x.
apply is_derive_unique.
Admitted.

Lemma is_derive_id : forall x : K, is_derive (fun t : K => t) x one.
Proof.
intros x.
apply filterdiff_ext_lin with (fun t : K => t).
apply filterdiff_id.
rewrite /scal /=.
intros y.
Admitted.

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
ring.

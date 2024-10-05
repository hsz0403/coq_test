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
Admitted.

Lemma is_derive_unique f x l : is_derive f x l -> Derive f x = l.
Proof.
intros H.
apply (@f_equal _ _ real _ l).
apply is_lim_unique.
apply is_lim_spec.
apply is_derive_Reals in H.
intros eps.
destruct (H eps (cond_pos _)) as [d Hd].
exists d => h.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= Ropp_0 Rplus_0_r.
intros Hu Zu.
Admitted.

Lemma Derive_correct f x : ex_derive f x -> is_derive f x (Derive f x).
Proof.
intros (l,H).
cut (Derive f x = l).
intros ; rewrite H0 ; apply H.
Admitted.

Lemma ex_derive_Reals_0 (f : R -> R) (x : R) : ex_derive f x -> derivable_pt f x.
Proof.
move => Hf.
apply Derive_correct in Hf.
apply is_derive_Reals in Hf.
Admitted.

Lemma ex_derive_Reals_1 (f : R -> R) (x : R) : derivable_pt f x -> ex_derive f x.
Proof.
case => l Hf.
exists l.
Admitted.

Lemma Derive_Reals (f : R -> R) (x : R) (pr : derivable_pt f x) : derive_pt f x pr = Derive f x.
Proof.
apply sym_eq, is_derive_unique.
case: pr => /= l Hf.
Admitted.

Lemma is_derive_ext_loc : forall (f g : K -> V) (x : K) (l : V), locally x (fun t : K => f t = g t) -> is_derive f x l -> is_derive g x l.
Proof.
intros f g x l Heq Hf.
Admitted.

Lemma ex_derive_ext_loc : forall (f g : K -> V) (x : K), locally x (fun t : K => f t = g t) -> ex_derive f x -> ex_derive g x.
Proof.
intros f g x Hfg (l,Hf).
exists l.
Admitted.

Lemma is_derive_ext : forall (f g : K -> V) (x : K) (l : V), (forall t : K, f t = g t) -> is_derive f x l -> is_derive g x l.
Proof.
intros f g x l Heq Hf.
apply: filterdiff_ext_locally Hf.
Admitted.

Lemma ex_derive_ext : forall (f g : K -> V) (x : K), (forall t : K, f t = g t) -> ex_derive f x -> ex_derive g x.
Proof.
intros f g x Heq [l Hf].
Admitted.

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

Lemma is_derive_mult : forall (f g : R -> R) (x : R) (df dg : R), is_derive f x df -> is_derive g x dg -> is_derive (fun t : R => f t * g t) x (df * g x + f x * dg) .
Proof.
intros f g x df dg Df Dg.
eapply filterdiff_ext_lin.
apply @filterdiff_mult_fct with (2 := Df) (3 := Dg).
exact Rmult_comm.
rewrite /scal /= /mult /plus /= => y.
Admitted.

Lemma ex_derive_mult (f g : R -> R) (x : R) : ex_derive f x -> ex_derive g x -> ex_derive (fun x : R => f x * g x) x.
Proof.
move => [d1 H1] [d2 H2].
exists (d1 * g x + f x * d2).
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

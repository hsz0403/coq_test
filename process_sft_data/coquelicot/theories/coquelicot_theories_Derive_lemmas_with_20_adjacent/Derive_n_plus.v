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

Lemma extension_C1_ext (f df : R -> V) (a b : Rbar) : forall (x : R), Rbar_le a x -> Rbar_le x b -> (extension_C1 f df a b) x = f x.
Proof.
move => x Hax Hxb.
rewrite /extension_C1.
case: Rbar_le_dec => // _.
Admitted.

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
Admitted.

Lemma extension_C1_ex_derive (f df : R -> R) (a b : Rbar) : Rbar_le a b -> (forall x : R, Rbar_le a x -> Rbar_le x b -> ex_derive f x) -> forall x : R, ex_derive (extension_C1 f (Derive f) a b) x.
Proof.
intros Hab Df x.
eexists.
apply extension_C1_is_derive => //.
intros y Hay Hby.
Admitted.

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
Admitted.

Lemma is_derive_n_unique f n x l : is_derive_n f n x l -> Derive_n f n x = l.
Proof.
case n.
easy.
simpl; intros n0 H.
Admitted.

Lemma Derive_n_correct f n x : ex_derive_n f n x -> is_derive_n f n x (Derive_n f n x).
Proof.
case: n => /= [ | n] Hf.
by [].
Admitted.

Lemma Derive_n_ext_loc : forall f g n x, locally x (fun t => f t = g t) -> Derive_n f n x = Derive_n g n x.
Proof.
intros f g n x Heq.
pattern x ; apply locally_singleton.
induction n.
exact Heq.
apply locally_locally in IHn.
apply filter_imp with (2 := IHn) => {IHn}.
intros t H.
Admitted.

Lemma ex_derive_n_ext_loc : forall f g n x, locally x (fun t => f t = g t) -> ex_derive_n f n x -> ex_derive_n g n x.
Proof.
intros f g n x Heq.
case: n => /= [ | n].
by [].
apply ex_derive_ext_loc.
apply locally_locally in Heq.
apply filter_imp with (2 := Heq) => {Heq}.
Admitted.

Lemma is_derive_n_ext_loc : forall f g n x l, locally x (fun t => f t = g t) -> is_derive_n f n x l -> is_derive_n g n x l.
Proof.
intros f g n x l Heq.
case: n => /= [ | n].
move => <- ; apply sym_eq.
pattern x ; now apply locally_singleton.
apply is_derive_ext_loc.
apply locally_locally in Heq.
apply filter_imp with (2 := Heq) => {Heq}.
Admitted.

Lemma Derive_n_ext : forall f g n x, (forall t, f t = g t) -> Derive_n f n x = Derive_n g n x.
Proof.
intros f g n x Heq.
apply Derive_n_ext_loc.
Admitted.

Lemma ex_derive_n_ext : forall f g n x, (forall t, f t = g t) -> ex_derive_n f n x -> ex_derive_n g n x.
Proof.
intros f g n x Heq.
apply ex_derive_n_ext_loc.
Admitted.

Lemma is_derive_n_ext : forall f g n x l, (forall t, f t = g t) -> is_derive_n f n x l -> is_derive_n g n x l.
Proof.
intros f g n x l Heq.
apply is_derive_n_ext_loc.
Admitted.

Lemma Derive_n_comp: forall f n m x, Derive_n (Derive_n f m) n x = Derive_n f (n+m) x.
Proof.
intros f n m.
induction n.
now simpl.
simpl.
intros x.
Admitted.

Lemma is_derive_Sn (f : R -> R) (n : nat) (x l : R) : locally x (ex_derive f) -> (is_derive_n f (S n) x l <-> is_derive_n (Derive f) n x l).
Proof.
move => Hf.
case: n => /= [ | n].
split => H.
by apply is_derive_unique.
rewrite -H ; apply Derive_correct.
now apply locally_singleton.
split => Hf'.
-
apply is_derive_ext with (2 := Hf').
move => y ; rewrite (Derive_n_comp _ n 1%nat).
by (replace (n + 1)%nat with (S n) by ring).
-
apply is_derive_ext with (2 := Hf').
move => y ; rewrite (Derive_n_comp _ n 1%nat).
Admitted.

Lemma is_derive_n_const n a : forall x, is_derive_n (fun _ => a) (S n) x 0.
Proof.
elim: n => /= [ | n IH] x.
by apply @is_derive_const.
eapply is_derive_ext.
intros t ; apply sym_equal, is_derive_unique, IH.
Admitted.

Lemma ex_derive_n_const a n x: ex_derive_n (fun _ => a) n x.
Proof.
case: n => //= ; case => //= [ | n].
apply ex_derive_const.
eapply ex_derive_ext.
intros t ; apply sym_equal, is_derive_unique, is_derive_n_const.
Admitted.

Lemma Derive_n_const n a : forall x, Derive_n (fun _ => a) (S n) x = 0.
Proof.
Admitted.

Lemma Derive_n_opp (f : R -> R) (n : nat) (x : R) : Derive_n (fun x => - f x) n x = - Derive_n f n x.
Proof.
elim: n x => [ | n IH] x /=.
by [].
rewrite -Derive_opp.
Admitted.

Lemma ex_derive_n_opp (f : R -> R) (n : nat) (x : R) : ex_derive_n f n x -> ex_derive_n (fun x => -f x) n x.
Proof.
case: n x => [ | n] /= x Hf.
by [].
apply ex_derive_opp in Hf.
apply: ex_derive_ext Hf.
Admitted.

Lemma is_derive_n_opp (f : R -> R) (n : nat) (x l : R) : is_derive_n f n x l -> is_derive_n (fun x => -f x) n x (- l).
Proof.
case: n x => [ | n] /= x Hf.
by rewrite Hf.
apply is_derive_opp in Hf.
apply: is_derive_ext Hf.
Admitted.

Lemma ex_derive_n_plus (f g : R -> R) (n : nat) (x : R) : locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) -> locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) -> ex_derive_n (fun x => f x + g x) n x.
Proof.
case: n x => /= [ | n] x Hf Hg.
by [].
apply ex_derive_ext_loc with (fun y => Derive_n f n y + Derive_n g n y).
apply locally_locally in Hf.
apply locally_locally in Hg.
generalize (filter_and _ _ Hf Hg).
apply filter_imp => {Hf Hg} y [Hf Hg].
apply sym_eq, Derive_n_plus.
apply filter_imp with (2 := Hf) ; by intuition.
apply filter_imp with (2 := Hg) ; by intuition.
apply: ex_derive_plus.
apply locally_singleton ; apply filter_imp with (2 := Hf) => {Hf} y Hy ; by apply (Hy (S n)).
Admitted.

Lemma is_derive_n_plus (f g : R -> R) (n : nat) (x lf lg : R) : locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) -> locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) -> is_derive_n f n x lf -> is_derive_n g n x lg -> is_derive_n (fun x => f x + g x) n x (lf + lg).
Proof.
case: n x lf lg => /= [ | n] x lf lg Hfn Hgn Hf Hg.
by rewrite Hf Hg.
apply is_derive_ext_loc with (fun y => Derive_n f n y + Derive_n g n y).
apply locally_locally in Hfn.
apply locally_locally in Hgn.
generalize (filter_and _ _ Hfn Hgn).
apply filter_imp => {Hfn Hgn} y [Hfn Hgn].
apply sym_eq, Derive_n_plus.
apply filter_imp with (2 := Hfn) ; by intuition.
apply filter_imp with (2 := Hgn) ; by intuition.
Admitted.

Lemma is_derive_n_iter_plus {I : Type} (l : list I) (f : I -> R -> R) (n: nat) (x : R) : locally x (fun y => forall (j : I) (k : nat), List.In j l -> (k <= n)%nat -> ex_derive_n (f j) k y) -> is_derive_n (fun y => iter Rplus 0 l (fun j => f j y)) n x (iter Rplus 0 l (fun j => Derive_n (f j) n x)).
Proof.
intros H.
elim: n {-2}n x (le_refl n) H => [ | n IH] m x Hn Hx.
now replace m with O by intuition.
apply le_lt_eq_dec in Hn ; case: Hn => Hn.
apply IH => //.
by apply lt_n_Sm_le.
rewrite Hn in Hx |- * => {m Hn} /=.
eapply is_derive_ext_loc.
eapply filter_imp.
intros y Hy.
apply sym_equal, is_derive_n_unique.
apply IH.
by apply le_refl.
apply Hy.
apply locally_locally.
move: Hx ; apply filter_imp.
move => y Hy j k Hj Hk.
apply Hy => //.
now eapply le_trans, le_n_Sn.
eapply filterdiff_ext_lin.
apply @filterdiff_iter_plus_fct => //.
apply locally_filter.
intros.
apply Derive_correct.
apply ((locally_singleton _ _ Hx) j (S n) H (le_refl _)).
simpl => y.
clear ; elim: l => /= [ | h l IH].
by rewrite scal_zero_r.
Admitted.

Lemma ex_derive_n_iter_plus {I : Type} (l : list I) (f : I -> R -> R) (n: nat) (x : R) : locally x (fun y => forall (j : I) (k : nat), List.In j l -> (k <= n)%nat -> ex_derive_n (f j) k y) -> ex_derive_n (fun y => iter Rplus 0 l (fun j => f j y)) n x.
Proof.
case: n => //= n H.
eexists.
Admitted.

Lemma Derive_n_iter_plus {I : Type} (l : list I) (f : I -> R -> R) (n: nat) (x : R) : locally x (fun y => forall (j : I) (k : nat), List.In j l -> (k <= n)%nat -> ex_derive_n (f j) k y) -> Derive_n (fun y => iter Rplus 0 l (fun j => f j y)) n x = iter Rplus 0 l (fun j => Derive_n (f j) n x).
Proof.
intros H.
apply is_derive_n_unique.
Admitted.

Lemma is_derive_n_sum_n_m n m (f : nat -> R -> R) (k: nat) (x : R) : locally x (fun t => forall l j , (n <= l <= m)%nat ->(j <= k)%nat -> ex_derive_n (f l) j t) -> is_derive_n (fun y => sum_n_m (fun j => f j y) n m) k x (sum_n_m (fun j => Derive_n (f j) k x) n m).
Proof.
intros.
apply is_derive_n_iter_plus.
move: H ; apply filter_imp ; intros.
apply H => //.
Admitted.

Lemma ex_derive_n_sum_n_m n m (f : nat -> R -> R) (k: nat) (x : R) : locally x (fun t => forall l j , (n <= l <= m)%nat ->(j <= k)%nat -> ex_derive_n (f l) j t) -> ex_derive_n (fun y => sum_n_m (fun j => f j y) n m) k x.
Proof.
intros.
apply ex_derive_n_iter_plus.
move: H ; apply filter_imp ; intros.
apply H => //.
Admitted.

Lemma Derive_n_sum_n_m n m (f : nat -> R -> R) (k: nat) (x : R) : locally x (fun t => forall l j , (n <= l <= m)%nat ->(j <= k)%nat -> ex_derive_n (f l) j t) -> Derive_n (fun y => sum_n_m (fun j => f j y) n m) k x = sum_n_m (fun j => Derive_n (f j) k x) n m.
Proof.
intros.
apply Derive_n_iter_plus.
move: H ; apply filter_imp ; intros.
apply H => //.
Admitted.

Lemma is_derive_n_sum_n n (f : nat -> R -> R) (k: nat) (x : R) : locally x (fun t => forall l j , (l <= n)%nat ->(j <= k)%nat -> ex_derive_n (f l) j t) -> is_derive_n (fun y => sum_n (fun j => f j y) n) k x (sum_n (fun j => Derive_n (f j) k x) n).
Proof.
intros.
apply is_derive_n_sum_n_m.
move: H ; apply filter_imp ; intros.
apply H => //.
Admitted.

Lemma ex_derive_n_sum_n n (f : nat -> R -> R) (k: nat) (x : R) : locally x (fun t => forall l j , (l <= n)%nat ->(j <= k)%nat -> ex_derive_n (f l) j t) -> ex_derive_n (fun y => sum_n (fun j => f j y) n) k x.
Proof.
intros.
apply ex_derive_n_sum_n_m.
move: H ; apply filter_imp ; intros.
apply H => //.
Admitted.

Lemma Derive_n_sum_n n (f : nat -> R -> R) (k: nat) (x : R) : locally x (fun t => forall l j , (l <= n)%nat ->(j <= k)%nat -> ex_derive_n (f l) j t) -> Derive_n (fun y => sum_n (fun j => f j y) n) k x = (sum_n (fun j => Derive_n (f j) k x) n).
Proof.
intros.
apply Derive_n_sum_n_m.
move: H ; apply filter_imp ; intros.
apply H => //.
Admitted.

Lemma Derive_n_minus (f g : R -> R) (n : nat) (x : R) : locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) -> locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) -> Derive_n (fun x => f x - g x) n x = Derive_n f n x - Derive_n g n x.
Proof.
move => Hf Hg.
rewrite Derive_n_plus.
by rewrite Derive_n_opp.
by [].
move: Hg ; apply filter_imp => y Hg k Hk.
Admitted.

Lemma ex_derive_n_minus (f g : R -> R) (n : nat) (x : R) : locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) -> locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) -> ex_derive_n (fun x => f x - g x) n x.
Proof.
move => Hf Hg.
apply ex_derive_n_plus.
by [].
move: Hg ; apply filter_imp => y Hg k Hk.
Admitted.

Lemma is_derive_n_minus (f g : R -> R) (n : nat) (x lf lg : R) : locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) -> locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) -> is_derive_n f n x lf -> is_derive_n g n x lg -> is_derive_n (fun x => f x - g x) n x (lf - lg).
Proof.
move => Hf Hg Df Dg.
apply is_derive_n_plus.
by [].
move: Hg ; apply filter_imp => y Hg k Hk.
apply ex_derive_n_opp ; by apply Hg.
by [].
Admitted.

Lemma Derive_n_scal_l (f : R -> R) (n : nat) (a x : R) : Derive_n (fun y => a * f y) n x = a * Derive_n f n x.
Proof.
elim: n x => /= [ | n IH] x.
by [].
rewrite -Derive_scal.
Admitted.

Lemma ex_derive_n_scal_l (f : R -> R) (n : nat) (a x : R) : ex_derive_n f n x -> ex_derive_n (fun y => a * f y) n x.
Proof.
case: n x => /= [ | n] x Hf.
by [].
apply ex_derive_ext with (fun y => a * Derive_n f n y).
move => t ; by rewrite Derive_n_scal_l.
Admitted.

Lemma is_derive_n_scal_l (f : R -> R) (n : nat) (a x l : R) : is_derive_n f n x l -> is_derive_n (fun y => a * f y) n x (a * l).
Proof.
case: n x => /= [ | n] x Hf.
by rewrite Hf.
eapply filterdiff_ext_lin.
apply filterdiff_ext with (fun y => a * Derive_n f n y).
move => t ; by rewrite Derive_n_scal_l.
apply @filterdiff_scal_r_fct ; try by apply locally_filter.
by apply Rmult_comm.
apply Hf.
move => /= y.
rewrite /scal /= /mult /=.
Admitted.

Lemma Derive_n_scal_r (f : R -> R) (n : nat) (a x : R) : Derive_n (fun y => f y * a) n x = Derive_n f n x * a.
Proof.
rewrite Rmult_comm -Derive_n_scal_l.
Admitted.

Lemma ex_derive_n_scal_r (f : R -> R) (n : nat) (a x : R) : ex_derive_n f n x -> ex_derive_n (fun y => f y * a) n x.
Proof.
move/(ex_derive_n_scal_l _ _ a).
Admitted.

Lemma is_derive_n_scal_r (f : R -> R) (n : nat) (a x l : R) : is_derive_n f n x l -> is_derive_n (fun y => f y * a) n x (l * a).
Proof.
move/(is_derive_n_scal_l _ _ a).
rewrite Rmult_comm.
Admitted.

Lemma Derive_n_plus (f g : R -> R) (n : nat) (x : R) : locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) -> locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) -> Derive_n (fun x => f x + g x) n x = Derive_n f n x + Derive_n g n x.
Proof.
elim: n x => /= [ | n IH] x [rf Hf] [rg Hg].
by [].
rewrite -Derive_plus.
apply Derive_ext_loc.
set r := (mkposreal _ (Rmin_stable_in_posreal rf rg)) ; exists r => y Hy.
rewrite /ball /= /AbsRing_ball /= in Hy.
apply Rabs_lt_between' in Hy.
case: Hy ; move/Rlt_Rminus => Hy1 ; move/Rlt_Rminus => Hy2.
set r0 := mkposreal _ (Rmin_pos _ _ Hy1 Hy2).
apply IH ; exists r0 => z Hz k Hk.
apply Hf.
rewrite /ball /= /AbsRing_ball /= in Hz.
apply Rabs_lt_between' in Hz.
rewrite /Rminus -Rmax_opp_Rmin Rplus_max_distr_l (Rplus_min_distr_l y) in Hz.
case: Hz ; move => Hz1 Hz2.
apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1 ; ring_simplify in Hz1.
apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2 ; ring_simplify (y + (x + Rmin rf rg + - y)) in Hz2.
have Hz := (conj Hz1 Hz2) => {Hz1 Hz2}.
apply Rabs_lt_between' in Hz.
apply Rlt_le_trans with (1 := Hz) => /= ; by apply Rmin_l.
by apply le_trans with (1 := Hk), le_n_Sn.
apply Hg.
rewrite /ball /= /AbsRing_ball /= in Hz.
apply Rabs_lt_between' in Hz.
rewrite /Rminus -Rmax_opp_Rmin Rplus_max_distr_l (Rplus_min_distr_l y) in Hz.
case: Hz ; move => Hz1 Hz2.
apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1 ; ring_simplify in Hz1.
apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2 ; ring_simplify (y + (x + Rmin rf rg + - y)) in Hz2.
have Hz := (conj Hz1 Hz2) => {Hz1 Hz2}.
apply Rabs_lt_between' in Hz.
apply Rlt_le_trans with (1 := Hz) => /= ; by apply Rmin_r.
by apply le_trans with (1 := Hk), le_n_Sn.
apply Hf with (k := (S n)).
by apply ball_center.
by apply le_refl.
apply Hg with (k := S n).
by apply ball_center.
by apply le_refl.

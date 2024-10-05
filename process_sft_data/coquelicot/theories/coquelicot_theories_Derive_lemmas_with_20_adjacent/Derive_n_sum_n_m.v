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

Lemma Derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x : R) : locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) -> Derive_n (fun y => f (a * y)) n x = (a ^ n * Derive_n f n (a * x)).
Proof.
case: (Req_dec a 0) => [ -> _ | Ha] /=.
rewrite Rmult_0_l.
elim: n x => [ | n IH] x /= ; rewrite ?Rmult_0_l.
ring.
rewrite (Derive_ext _ _ _ IH).
by apply Derive_const.
move => Hf.
apply (locally_singleton _ (fun x => Derive_n (fun y : R => f (a * y)) n x = a ^ n * Derive_n f n (a * x))).
elim: n Hf => [ | n IH] Hf.
apply filter_forall => /= y ; ring.
case: IH => [ | r IH].
case: Hf => r0 Hf.
exists r0 => y Hy k Hk ; by intuition.
case: Hf => r0 Hf.
have Hr1 : 0 < Rmin (r0 / (Rabs a)) r.
apply Rmin_case.
apply Rdiv_lt_0_compat.
by apply r0.
by apply Rabs_pos_lt.
by apply r.
set r1 := mkposreal _ Hr1.
exists r1 => y Hy /=.
rewrite (Derive_ext_loc _ (fun y => a ^ n * Derive_n f n (a * y))).
rewrite Derive_scal.
rewrite (Rmult_comm a (a^n)) Rmult_assoc.
apply f_equal.
rewrite Derive_comp.
rewrite (Derive_ext (Rmult a) (fun x => a * x)) => //.
rewrite Derive_scal Derive_id ; ring.
apply Hf with (k := S n).
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /=.
rewrite -/(Rminus _ _) -Rmult_minus_distr_l Rabs_mult.
apply Rlt_le_trans with (Rabs a * r1).
apply Rmult_lt_compat_l.
by apply Rabs_pos_lt.
by apply Hy.
rewrite Rmult_comm ; apply Rle_div_r.
by apply Rabs_pos_lt.
rewrite /r1 ; by apply Rmin_l.
by apply lt_n_Sn.
apply ex_derive_scal.
by apply ex_derive_id.
rewrite /ball /= /AbsRing_ball /= in Hy.
apply Rabs_lt_between' in Hy.
case: Hy => Hy1 Hy2.
apply Rlt_Rminus in Hy1.
apply Rlt_Rminus in Hy2.
have Hy : 0 < Rmin (y - (x - r1)) (x + r1 - y).
by apply Rmin_case.
exists (mkposreal (Rmin (y - (x - r1)) (x + r1 - y)) Hy).
set r2 := Rmin (y - (x - r1)) (x + r1 - y).
move => t Ht.
apply IH.
apply Rabs_lt_between'.
rewrite /ball /= /AbsRing_ball /= in Ht.
apply Rabs_lt_between' in Ht.
simpl in Ht.
split.
apply Rle_lt_trans with (2 := proj1 Ht).
rewrite /r2 ; apply Rle_trans with (y-(y-(x-r1))).
ring_simplify ; apply Rplus_le_compat_l, Ropp_le_contravar.
rewrite /r1 ; apply Rmin_r.
apply Rplus_le_compat_l, Ropp_le_contravar, Rmin_l.
apply Rlt_le_trans with (1 := proj2 Ht).
rewrite /r2 ; apply Rle_trans with (y+((x+r1)-y)).
apply Rplus_le_compat_l, Rmin_r.
ring_simplify ; apply Rplus_le_compat_l.
Admitted.

Lemma ex_derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x : R) : locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) -> ex_derive_n (fun y => f (a * y)) n x.
Proof.
case: n f x => /= [ | n] f x Hf.
by [].
case: (Req_dec a 0) => Ha.
rewrite Ha => {a Ha Hf}.
apply ex_derive_ext with (fun _ => Derive_n (fun y : R => f (0 * y)) n 0).
elim: n => /= [ | n IH] t.
by rewrite ?Rmult_0_l.
rewrite -?(Derive_ext _ _ _ IH).
by rewrite ?Derive_const.
by apply ex_derive_const.
apply ex_derive_ext_loc with (fun x => a^n * Derive_n f n (a * x)).
case: Hf => r Hf.
have Hr0 : 0 < r / Rabs a.
apply Rdiv_lt_0_compat.
by apply r.
by apply Rabs_pos_lt.
exists (mkposreal _ Hr0) => /= y Hy.
apply eq_sym, Derive_n_comp_scal.
have : Rabs (a*y - a*x) < r.
rewrite -Rmult_minus_distr_l Rabs_mult.
replace (pos r) with (Rabs a * (r / Rabs a)) by (field ; by apply Rgt_not_eq, Rabs_pos_lt).
apply Rmult_lt_compat_l.
by apply Rabs_pos_lt.
by apply Hy.
move => {Hy} Hy.
apply Rabs_lt_between' in Hy ; case: Hy => Hy1 Hy2.
apply Rlt_Rminus in Hy1.
apply Rlt_Rminus in Hy2.
exists (mkposreal _ (Rmin_pos _ _ Hy1 Hy2)) => /= z Hz k Hk.
rewrite /ball /= /AbsRing_ball /= in Hz.
apply Rabs_lt_between' in Hz ; case: Hz => Hz1 Hz2.
rewrite /Rminus -Rmax_opp_Rmin in Hz1.
rewrite Rplus_min_distr_l in Hz2.
apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2.
ring_simplify in Hz2.
rewrite Rplus_max_distr_l in Hz1.
apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1.
ring_simplify in Hz1.
apply Hf.
apply Rabs_lt_between' ; by split.
by intuition.
apply ex_derive_scal.
apply ex_derive_comp.
apply (locally_singleton _ _) in Hf.
by apply Hf with (k := S n).
Admitted.

Lemma is_derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x l : R) : locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) -> is_derive_n f n (a * x) l -> is_derive_n (fun y => f (a * y)) n x (a ^ n * l).
Proof.
case: n => /= [ | n] Hfn Hf.
by rewrite Rmult_1_l.
apply is_derive_unique in Hf.
rewrite -Hf.
rewrite -(Derive_n_comp_scal f a (S n) x) => //.
apply Derive_correct.
Admitted.

Lemma Derive_n_comp_opp (f : R -> R) (n : nat) (x : R) : locally (- x) (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) -> Derive_n (fun y => f (- y)) n x = ((-1) ^ n * Derive_n f n (-x)).
Proof.
move => Hf.
rewrite -(Derive_n_ext (fun y : R => f (-1 * y))).
rewrite (Derive_n_comp_scal f (-1) n x).
by replace (-1*x) with (-x) by ring.
by replace (-1*x) with (-x) by ring.
Admitted.

Lemma ex_derive_n_comp_opp (f : R -> R) (n : nat) (x : R) : locally (- x) (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) -> ex_derive_n (fun y => f (- y)) n x.
Proof.
move => Hf.
apply (ex_derive_n_ext (fun y : R => f (-1 * y))).
move => t ; by ring_simplify (-1*t).
apply (ex_derive_n_comp_scal f (-1) n x).
Admitted.

Lemma is_derive_n_comp_opp (f : R -> R) (n : nat) (x l : R) : locally (- x) (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) -> is_derive_n f n (-x) l -> is_derive_n (fun y => f (- y)) n x ((-1)^n * l).
Proof.
move => Hfn Hf.
apply (is_derive_n_ext (fun y : R => f (-1 * y))).
move => t ; by ring_simplify (-1*t).
apply (is_derive_n_comp_scal f (-1) n x).
by replace (-1*x) with (-x) by ring.
Admitted.

Lemma Derive_n_comp_trans (f : R -> R) (n : nat) (x b : R) : Derive_n (fun y => f (y + b)) n x = Derive_n f n (x + b).
Proof.
elim: n x => [ | n IH] x /=.
by [].
rewrite (Derive_ext _ _ _ IH) => {IH}.
generalize (Derive_n f n) => {f} f.
apply (f_equal real).
apply Lim_ext => y.
replace (x + b + y) with (x + y + b) by ring.
Admitted.

Lemma ex_derive_n_comp_trans (f : R -> R) (n : nat) (x b : R) : ex_derive_n f n (x + b) -> ex_derive_n (fun y => f (y + b)) n x.
Proof.
case: n => [ | n] /= Df.
by [].
apply ex_derive_ext with (fun x => Derive_n f n (x + b)).
simpl => t.
apply sym_eq, Derive_n_comp_trans.
move: (Derive_n f n) Df => {f} f Df.
apply ex_derive_comp.
apply Df.
apply: ex_derive_plus.
apply ex_derive_id.
Admitted.

Lemma Derive_n_sum_n_m n m (f : nat -> R -> R) (k: nat) (x : R) : locally x (fun t => forall l j , (n <= l <= m)%nat ->(j <= k)%nat -> ex_derive_n (f l) j t) -> Derive_n (fun y => sum_n_m (fun j => f j y) n m) k x = sum_n_m (fun j => Derive_n (f j) k x) n m.
Proof.
intros.
apply Derive_n_iter_plus.
move: H ; apply filter_imp ; intros.
apply H => //.
by apply In_iota.

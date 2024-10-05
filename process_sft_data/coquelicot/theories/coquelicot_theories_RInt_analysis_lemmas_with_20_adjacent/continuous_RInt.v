Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq Derive SF_seq.
Require Import Continuity Hierarchy Seq_fct RInt PSeries.
Section Continuity.
Context {V : NormedModule R_AbsRing}.
End Continuity.
Section Derive.
Context {V : NormedModule R_AbsRing}.
End Derive.
Section Derive'.
Context {V : CompleteNormedModule R_AbsRing}.
End Derive'.
Section Comp.
Context {V : CompleteNormedModule R_AbsRing}.
End Comp.
Section RInt_comp.
Context {V : NormedModule R_AbsRing}.
End RInt_comp.
Definition PS_Int (a : nat -> R) (n : nat) : R := match n with | O => 0 | S n => a n / INR (S n) end.
Section ByParts.
Context {V : CompleteNormedModule R_AbsRing}.
End ByParts.

Lemma continuous_RInt_0 : forall (f : R -> V) (a : R) If, locally a (fun x => is_RInt f a x (If x)) -> continuous If a.
Admitted.

Lemma continuous_RInt_1 (f : R -> V) (a b : R) (If : R -> V) : locally b (fun z : R => is_RInt f a z (If z)) -> continuous If b.
Proof.
intros.
generalize (locally_singleton _ _ H) => /= Hab.
apply continuous_ext with (fun z => plus (If b) (minus (If z) (If b))) ; simpl.
intros x.
by rewrite plus_comm -plus_assoc plus_opp_l plus_zero_r.
eapply filterlim_comp_2, filterlim_plus.
apply filterlim_const.
apply (continuous_RInt_0 f _ (fun x : R_UniformSpace => minus (If x) (If b))).
apply: filter_imp H => x Hx.
rewrite /minus plus_comm.
eapply is_RInt_Chasles, Hx.
Admitted.

Lemma continuous_RInt_2 (f : R -> V) (a b : R) (If : R -> V) : locally a (fun z : R => is_RInt f z b (If z)) -> continuous If a.
Proof.
intros.
generalize (locally_singleton _ _ H) => /= Hab.
apply continuous_ext with (fun z => opp (plus (opp (If a)) (minus (If a) (If z)))) ; simpl.
intros x.
by rewrite /minus plus_assoc plus_opp_l plus_zero_l opp_opp.
apply continuous_opp.
apply continuous_plus.
apply filterlim_const.
apply (continuous_RInt_0 f _ (fun x : R_UniformSpace => minus (If a) (If x))).
apply: filter_imp H => x Hx.
eapply is_RInt_Chasles.
by apply Hab.
Admitted.

Lemma ex_RInt_locally {V : CompleteNormedModule R_AbsRing} (f : R -> V) (a b : R) : ex_RInt f a b -> (exists eps : posreal, ex_RInt f (a - eps) (a + eps)) -> (exists eps : posreal, ex_RInt f (b - eps) (b + eps)) -> locally (a,b) (fun z : R * R => ex_RInt f (fst z) (snd z)).
Proof.
intros Hf (ea,Hea) (eb,Heb).
exists (mkposreal _ (Rmin_stable_in_posreal ea eb)) => [[a' b'] [Ha' Hb']] ; simpl in *.
apply ex_RInt_Chasles with (a - ea).
eapply ex_RInt_swap, ex_RInt_Chasles_1 ; try eassumption.
apply Rabs_le_between'.
eapply Rlt_le, Rlt_le_trans, Rmin_l.
by apply Ha'.
apply ex_RInt_Chasles with a.
eapply ex_RInt_Chasles_1 ; try eassumption.
apply Rabs_le_between'.
rewrite Rminus_eq_0 Rabs_R0.
by apply Rlt_le, ea.
apply ex_RInt_Chasles with b => //.
apply ex_RInt_Chasles with (b - eb).
eapply ex_RInt_swap, ex_RInt_Chasles_1; try eassumption.
apply Rabs_le_between'.
rewrite Rminus_eq_0 Rabs_R0.
by apply Rlt_le, eb.
eapply ex_RInt_Chasles_1 ; try eassumption.
apply Rabs_le_between'.
eapply Rlt_le, Rlt_le_trans, Rmin_r.
Admitted.

Lemma is_derive_RInt_0 (f If : R -> V) (a : R) : locally a (fun b => is_RInt f a b (If b)) -> continuous f a -> is_derive If a (f a).
Proof.
intros HIf Hf.
split ; simpl.
apply is_linear_scal_l.
intros y Hy.
apply @is_filter_lim_locally_unique in Hy.
rewrite -Hy {y Hy}.
intros eps.
generalize (proj1 (filterlim_locally _ _) Hf) => {Hf} Hf.
eapply filter_imp.
simpl ; intros y Hy.
replace (If a) with (@zero V).
rewrite @minus_zero_r.
rewrite Rmult_comm ; eapply norm_RInt_le_const_abs ; last first.
apply is_RInt_minus.
instantiate (1 := f).
eapply (proj1 Hy).
apply is_RInt_const.
simpl.
apply (proj2 Hy).
apply locally_singleton in HIf.
set (HIf_0 := is_RInt_point f a).
apply (filterlim_locally_unique _ _ _ HIf_0 HIf).
apply filter_and.
by apply HIf.
assert (0 < eps / @norm_factor _ V).
apply Rdiv_lt_0_compat.
by apply eps.
by apply norm_factor_gt_0.
case: (Hf (mkposreal _ H)) => {Hf} delta Hf.
exists delta ; intros y Hy z Hz.
eapply Rle_trans.
apply Rlt_le, norm_compat2.
apply Hf.
apply Rabs_lt_between'.
move/Rabs_lt_between': Hy => Hy.
rewrite /Rmin /Rmax in Hz ; destruct (Rle_dec a y) as [Hxy | Hxy].
split.
eapply Rlt_le_trans, Hz.
apply Rminus_lt_0 ; ring_simplify.
by apply delta.
eapply Rle_lt_trans, Hy.
by apply Hz.
split.
eapply Rlt_le_trans, Hz.
by apply Hy.
eapply Rle_lt_trans.
apply Hz.
apply Rminus_lt_0 ; ring_simplify.
by apply delta.
simpl ; apply Req_le.
field.
Admitted.

Lemma is_derive_RInt (f If : R -> V) (a b : R) : locally b (fun b => is_RInt f a b (If b)) -> continuous f b -> is_derive If b (f b).
Proof.
intros HIf Hf.
apply is_derive_ext with (fun y => (plus (minus (If y) (If b)) (If b))).
simpl ; intros.
rewrite /minus -plus_assoc plus_opp_l.
by apply plus_zero_r.
evar_last.
apply is_derive_plus.
apply is_derive_RInt_0.
2: apply Hf.
eapply filter_imp.
intros y Hy.
evar_last.
apply is_RInt_Chasles with a.
apply is_RInt_swap.
3: by apply plus_comm.
by apply locally_singleton in HIf.
by apply Hy.
by apply HIf.
apply is_derive_const.
Admitted.

Lemma is_derive_RInt' (f If : R -> V) (a b : R) : locally a (fun a => is_RInt f a b (If a)) -> continuous f a -> is_derive If a (opp (f a)).
Proof.
intros.
apply is_derive_ext with (fun x => opp (opp (If x))).
intros ; by rewrite opp_opp.
apply is_derive_opp.
apply is_derive_RInt with b => //.
move: H ; apply filter_imp.
intros x Hx.
Admitted.

Lemma filterdiff_RInt (f : R -> V) (If : R -> R -> V) (a b : R) : locally (a,b) (fun u : R * R => is_RInt f (fst u) (snd u) (If (fst u) (snd u))) -> continuous f a -> continuous f b -> filterdiff (fun u : R * R => If (fst u) (snd u)) (locally (a,b)) (fun u : R * R => minus (scal (snd u) (f b)) (scal (fst u) (f a))).
Proof.
intros Hf Cfa Cfb.
assert (Ha : locally a (fun a : R => is_RInt f a b (If a b))).
case: Hf => /= e He.
exists e => x Hx.
apply (He (x,b)).
split => //.
by apply ball_center.
assert (Hb : locally b (fun b : R => is_RInt f a b (If a b))).
case: Hf => /= e He.
exists e => x Hx.
apply (He (a,x)).
split => //.
by apply ball_center.
eapply filterdiff_ext_lin.
apply (filterdiff_ext_loc (FF := @filter_filter _ _ (locally_filter _)) (fun u : R * R => plus (If (fst u) b) (minus (If a (snd u)) (If a b)))) ; last first.
apply filterdiff_plus_fct.
apply (filterdiff_comp' (fun u : R * R => fst u) (fun a : R => If a b)).
by apply filterdiff_linear, is_linear_fst.
eapply is_derive_RInt', Cfa.
by apply Ha.
apply filterdiff_plus_fct.
apply (filterdiff_comp' (fun u : R * R => snd u) (fun b : R => If a b)).
by apply filterdiff_linear, is_linear_snd.
eapply is_derive_RInt, Cfb.
by apply Hb.
apply filterdiff_const.
move => /= x Hx.
apply @is_filter_lim_locally_unique in Hx.
by rewrite -Hx /= minus_eq_zero plus_zero_r.
simpl.
have : (locally (a,b) (fun u : R * R => is_RInt f (fst u) b (If (fst u) b))) => [ | {Ha} Ha].
case: Ha => /= e He.
exists e => y Hy.
apply He, Hy.
have : (locally (a,b) (fun u : R * R => is_RInt f a (snd u) (If a (snd u)))) => [ | {Hb} Hb].
case: Hb => /= e He.
exists e => y Hy.
apply He, Hy.
move: (locally_singleton _ _ Hf) => /= Hab.
generalize (filter_and _ _ Hf (filter_and _ _ Ha Hb)).
apply filter_imp => {Hf Ha Hb} /= u [Hf [Ha Hb]].
apply sym_eq, (filterlim_locally_unique _ _ _ Hf).
apply is_RInt_Chasles with b => //.
rewrite /minus plus_comm.
apply is_RInt_Chasles with a => //.
by apply is_RInt_swap.
simpl => y.
rewrite scal_opp_r plus_zero_r.
Admitted.

Lemma Derive_RInt (f : R -> R) (a b : R) : locally b (ex_RInt f a) -> continuous f b -> Derive (RInt f a) b = f b.
Proof.
intros If Cf.
apply is_derive_unique, (is_derive_RInt _ _ a) => //.
move: If ; apply filter_imp => y.
Admitted.

Lemma Derive_RInt' (f : R -> R) (a b : R) : locally a (fun a => ex_RInt f a b) -> continuous f a -> Derive (fun a => RInt f a b) a = - f a.
Proof.
intros If Cf.
eapply is_derive_unique, (is_derive_RInt' (V := R_NormedModule) _ _ a b) => //.
move: If ; apply filter_imp => y.
Admitted.

Lemma is_RInt_derive (f df : R -> V) (a b : R) : (forall x : R, Rmin a b <= x <= Rmax a b -> is_derive f x (df x)) -> (forall x : R, Rmin a b <= x <= Rmax a b -> continuous df x) -> is_RInt df a b (minus (f b) (f a)).
Proof.
intros Hf Hdf.
wlog Hab: a b Hf Hdf / (a < b).
intros H.
destruct (Rlt_or_le a b) as [Hab|Hab].
exact: H.
destruct Hab as [Hab|Hab].
+
rewrite -(opp_opp (minus _ _)).
apply: is_RInt_swap.
rewrite opp_minus.
apply H.
by rewrite Rmin_comm Rmax_comm.
by rewrite Rmin_comm Rmax_comm.
easy.
+
rewrite Hab.
rewrite /minus plus_opp_r.
by apply: is_RInt_point.
rewrite Rmin_left in Hf; last by lra.
rewrite Rmax_right in Hf; last by lra.
rewrite Rmin_left in Hdf; last by lra.
rewrite Rmax_right in Hdf; last by lra.
have Hminab : Rmin a b = a by rewrite Rmin_left; lra.
have Hmaxab : Rmax a b = b by rewrite Rmax_right; lra.
evar_last.
apply RInt_correct.
apply (ex_RInt_continuous df) => t Ht.
rewrite Hminab Hmaxab in Ht.
exact:Hdf.
apply (plus_reg_r (opp (f b))).
rewrite /minus -plus_assoc (plus_comm (opp _)) plus_assoc plus_opp_r.
rewrite -(RInt_point a df).
apply: sym_eq.
have Hext : forall x : R, Rmin a b < x < Rmax a b -> extension_C0 df a b x = df x.
move => x; rewrite Hminab Hmaxab => Hx.
by rewrite extension_C0_ext //=; lra.
rewrite -(RInt_ext _ _ _ _ Hext).
rewrite RInt_point -(RInt_point a (extension_C0 df a b)).
rewrite -!(extension_C1_ext f df a b) /=; try lra.
apply: (eq_is_derive (fun t => minus (RInt _ a t) (_ t))) => // t Ht.
have -> : zero = minus (extension_C0 df a b t) (extension_C0 df a b t) by rewrite minus_eq_zero.
apply: is_derive_minus; last first.
apply: extension_C1_is_derive => /=; first by lra.
by move => x Hax Hxb; apply: Hf; lra.
apply: (is_derive_RInt _ _ a).
apply: filter_forall.
move => x; apply: RInt_correct.
apply: ex_RInt_continuous.
move => z Hz; apply: extension_C0_continuous => /=; try lra.
by move => x0 Hax0 Hx0b; apply: Hdf; lra.
apply: extension_C0_continuous => /=; try lra.
Admitted.

Lemma RInt_Derive (f : R -> R) (a b : R): (forall x, Rmin a b <= x <= Rmax a b -> ex_derive f x) -> (forall x, Rmin a b <= x <= Rmax a b -> continuous (Derive f) x) -> RInt (Derive f) a b = f b - f a.
Proof.
intros Df Cdf.
apply is_RInt_unique.
apply: is_RInt_derive => //.
Admitted.

Lemma IVT_gen_consistent (f : R -> R) (a b y : R) : (forall x, continuous f x) -> Rmin (f a) (f b) <= y <= Rmax (f a) (f b) -> { x : R | Rmin a b <= x <= Rmax a b /\ f x = y }.
Proof.
move => Hf.
apply: IVT_gen.
move => x.
apply continuity_pt_filterlim.
Admitted.

Lemma continuous_ab_maj_consistent : forall (f : R -> R) (a b : R), a <= b -> (forall c : R, a <= c <= b -> continuous f c) -> exists Mx : R, (forall c : R, a <= c <= b -> f c <= f Mx) /\ a <= Mx <= b.
Proof.
move => f a b Hab Hc.
apply: continuity_ab_maj => // .
Admitted.

Lemma continuous_ab_min_consistent : forall (f : R -> R) (a b : R), a <= b -> (forall c : R, a <= c <= b -> continuous f c) -> exists mx : R, (forall c : R, a <= c <= b -> f mx <= f c) /\ a <= mx <= b.
Proof.
move => f a b Hab Hc.
apply: continuity_ab_min => // .
Admitted.

Lemma is_RInt_comp (f : R -> V) (g dg : R -> R) (a b : R) : (forall x, Rmin a b <= x <= Rmax a b -> continuous f (g x)) -> (forall x, Rmin a b <= x <= Rmax a b -> is_derive g x (dg x) /\ continuous dg x) -> is_RInt (fun y => scal (dg y) (f (g y))) a b (RInt f (g a) (g b)).
Proof.
wlog: a b / (a < b) => [Hw|Hab].
case: (total_order_T a b) => [[Hab'|Hab']|Hab'] Hf Hg.
-
exact: Hw.
-
rewrite Hab'.
by rewrite RInt_point; apply: is_RInt_point.
-
rewrite <- (opp_opp (RInt f _ _)).
apply: is_RInt_swap.
rewrite opp_RInt_swap.
apply Hw => // .
by rewrite Rmin_comm Rmax_comm.
by rewrite Rmin_comm Rmax_comm.
apply: ex_RInt_continuous => z Hz.
case: (IVT_gen_consistent (extension_C0 g b a) b a z).
+
apply: extension_C0_continuous => /=; try lra.
move => x Hbx Hxa; apply: ex_derive_continuous.
by exists (dg x); apply Hg; rewrite Rmin_right ?Rmax_left; try lra.
+
rewrite !(extension_C0_ext) /=; try lra.
by rewrite Rmin_comm Rmax_comm.
+
move => x [Hx1 Hx2].
rewrite -Hx2.
rewrite Rmin_left ?Rmax_right in Hx1; try lra.
rewrite (extension_C0_ext) /=; try lra.
apply: Hf.
by move: Hx1; rewrite Rmin_right ?Rmax_left; lra.
rewrite -> Rmin_left by now apply Rlt_le.
rewrite -> Rmax_right by now apply Rlt_le.
wlog: g dg / (forall x : R, is_derive g x (dg x) /\ continuous dg x) => [Hw Hf Hg | Hg Hf _].
rewrite -?(extension_C1_ext g dg a b) ; try by [left | right].
set g0 := extension_C1 g dg a b.
set dg0 := extension_C0 dg a b.
apply is_RInt_ext with (fun y : R => scal (dg0 y) (f (g0 y))).
+
rewrite /Rmin /Rmax /g0 ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hx.
apply f_equal2.
by apply extension_C0_ext ; by apply Rlt_le, Hx.
by apply f_equal, extension_C1_ext ; by apply Rlt_le, Hx.
+
apply Hw.
*
intros x ; split.
apply extension_C1_is_derive.
by apply Rlt_le.
by intros ; apply Hg ; by split.
*
apply @extension_C0_continuous.
by apply Rlt_le.
intros ; apply Hg ; by split.
*
intros ; rewrite /g0 extension_C1_ext.
by apply Hf.
by apply H.
by apply H.
intros ; split.
apply extension_C1_is_derive.
by apply Rlt_le.
intros ; apply Hg ; by split.
apply @extension_C0_continuous.
by apply Rlt_le.
by intros ; apply Hg ; by split.
have cg : forall x, continuous g x.
move => t Ht; apply: ex_derive_continuous.
by exists (dg t); apply Hg.
wlog: f Hf / (forall x, continuous f x) => [Hw | {Hf} Hf].
case: (continuous_ab_maj_consistent g a b (Rlt_le _ _ Hab)) => [ | M HM].
move => x Hx; apply: ex_derive_continuous.
by exists (dg x); apply Hg.
case: (continuous_ab_min_consistent g a b (Rlt_le _ _ Hab)) => [ | m Hm].
move => x Hx; apply: ex_derive_continuous.
by exists (dg x) ; apply Hg.
have H : g m <= g M.
by apply Hm ; intuition.
case: (C0_extension_le f (g m) (g M)) => [ y Hy | f0 Hf0].
+
case: (IVT_gen_consistent g m M y) => // .
rewrite /Rmin /Rmax ; case: Rle_dec => // .
move => x [Hx <-].
apply Hf ; split.
apply Rle_trans with (2 := proj1 Hx).
by apply Rmin_case ; intuition.
apply Rle_trans with (1 := proj2 Hx).
apply Rmax_case ; intuition.
apply is_RInt_ext with (fun y : R => scal (dg y) (f0 (g y))).
rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hc.
apply f_equal.
apply Hf0 ; split.
by apply Hm ; split ; apply Rlt_le ; apply Hc.
by apply HM ; split ; apply Rlt_le ; apply Hc.
rewrite -(RInt_ext f0).
+
apply Hw.
by move => x Hx ; apply Hf0.
by move => x ; apply Hf0.
+
move => x Hx.
case: (IVT_gen_consistent g a b x cg) => // .
by lra.
rewrite Rmin_left ?Rmax_right; try lra.
move => x0 Hx0.
case: Hx0 => Hx0 Hgx0x; rewrite -Hgx0x.
apply Hf0; split.
by apply Hm.
by apply HM.
evar_last.
+
apply (is_RInt_derive (fun x => RInt f (g a) (g x))).
move => x Hx.
evar_last.
apply is_derive_comp.
apply is_derive_RInt with (g a).
apply filter_forall => y.
apply RInt_correct, @ex_RInt_continuous.
by intros ; apply Hf.
by apply Hf.
by apply Hg.
reflexivity.
intros x Hx.
apply: @continuous_scal.
by apply Hg.
apply continuous_comp.
apply @ex_derive_continuous.
by eexists ; apply Hg.
by apply Hf.
+
Admitted.

Lemma RInt_comp (f : R -> V) (g dg : R -> R) (a b : R) : (forall x, Rmin a b <= x <= Rmax a b -> continuous f (g x)) -> (forall x, Rmin a b <= x <= Rmax a b -> is_derive g x (dg x) /\ continuous dg x) -> RInt (fun y => scal (dg y) (f (g y))) a b = RInt f (g a) (g b).
Proof.
move => Hfg Hg.
have H := (is_RInt_comp _ _ _ _ _ Hfg Hg).
Admitted.

Lemma RInt_Chasles_bound_comp_l_loc (f : R -> R -> R) (a : R -> R) (b x : R) : locally x (fun y => ex_RInt (f y) (a x) b) -> (exists eps : posreal, locally x (fun y => ex_RInt (f y) (a x - eps) (a x + eps))) -> continuous a x -> locally x (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) b = RInt (f x') (a x') b).
Proof.
intros Hab (eps,Hae) Ca.
generalize (proj1 (filterlim_locally _ _) Ca) => {Ca} Ca.
generalize (filter_and _ _ (Ca eps) (filter_and _ _ Hab Hae)).
apply filter_imp => {Ca Hae Hab} y [Hy [Hab Hae]].
apply RInt_Chasles with (2 := Hab).
apply ex_RInt_inside with (1 := Hae).
now apply Rlt_le.
rewrite /Rminus Rplus_opp_r Rabs_R0.
Admitted.

Lemma RInt_Chasles_bound_comp_loc (f : R -> R -> R) (a b : R -> R) (x : R) : locally x (fun y => ex_RInt (f y) (a x) (b x)) -> (exists eps : posreal, locally x (fun y => ex_RInt (f y) (a x - eps) (a x + eps))) -> (exists eps : posreal, locally x (fun y => ex_RInt (f y) (b x - eps) (b x + eps))) -> continuous a x -> continuous b x -> locally x (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) (b x') = RInt (f x') (a x') (b x')).
Proof.
intros Hab (ea,Hae) (eb,Hbe) Ca Cb.
generalize (proj1 (filterlim_locally _ _) Ca) => {Ca} Ca.
generalize (proj1 (filterlim_locally _ _) Cb) => {Cb} Cb.
set (e := mkposreal _ (Rmin_stable_in_posreal ea eb)).
generalize (filter_and _ _ (filter_and _ _ (Ca e) (Cb e)) (filter_and _ _ Hab (filter_and _ _ Hae Hbe))).
apply filter_imp => {Ca Cb Hab Hae Hbe} y [[Hay Hby] [Hab [Hae Hbe]]].
apply: RInt_Chasles.
apply ex_RInt_inside with (1 := Hae).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hay).
exact: Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply ex_RInt_Chasles with (1 := Hab).
apply ex_RInt_inside with (1 := Hbe).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hby).
Admitted.

Lemma is_derive_RInt_bound_comp (f : R -> V) (If : R -> R -> V) (a b : R -> R) (da db x : R) : locally (a x, b x) (fun u : R * R => is_RInt f (fst u) (snd u) (If (fst u) (snd u))) -> continuous f (a x) -> continuous f (b x) -> is_derive a x da -> is_derive b x db -> is_derive (fun x => If (a x) (b x)) x (minus (scal db (f (b x))) (scal da (f (a x)))).
Proof.
intros Iab Ca Cb Da Db.
unfold is_derive.
eapply filterdiff_ext_lin.
apply @filterdiff_comp'_2.
apply Da.
apply Db.
eapply filterdiff_ext_lin.
apply (filterdiff_RInt f If (a x) (b x)).
exact Iab.
exact Ca.
exact Cb.
by case => y z /=.
simpl => y.
Admitted.

Lemma is_derive_RInt_param_aux : forall (f : R -> R -> R) (a b x : R), locally x (fun x : R => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u : R => f u t) x) -> (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) -> locally x (fun y : R => ex_RInt (fun t => f y t) a b) -> ex_RInt (fun t => Derive (fun u => f u t) x) a b -> is_derive (fun x : R => RInt (fun t => f x t) a b) x (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x.
wlog: a b / a < b => H.
destruct (total_order_T a b) as [[Hab|Hab]|Hab].
now apply H.
intros _ _ _ _.
rewrite Hab.
rewrite RInt_point.
apply is_derive_ext with (fun _ => 0).
simpl => t.
apply sym_eq.
apply: RInt_point.
apply: is_derive_const.
simpl => H1 H2 H3 H4.
apply is_derive_ext_loc with (fun u => - RInt (fun t => f u t) b a).
apply: filter_imp H3 => t Ht.
apply: opp_RInt_swap.
exact: ex_RInt_swap.
eapply filterdiff_ext_lin.
apply @filterdiff_opp_fct ; try by apply locally_filter.
apply H.
exact Hab.
now rewrite Rmin_comm Rmax_comm.
now rewrite Rmin_comm Rmax_comm.
move: H3 ; apply filter_imp => y H3.
now apply ex_RInt_swap.
now apply ex_RInt_swap.
rewrite -opp_RInt_swap //=.
intros y.
by rewrite -scal_opp_r opp_opp.
rewrite Rmin_left.
2: now apply Rlt_le.
rewrite Rmax_right.
2: now apply Rlt_le.
intros Df Cdf If IDf.
split => [ | y Hy].
by apply @is_linear_scal_l.
rewrite -(is_filter_lim_locally_unique _ _ Hy) => {y Hy}.
assert (Cdf'' : forall t : R, a <= t <= b -> continuity_2d_pt (fun u v : R => Derive (fun z : R => f z u) v) t x).
intros t Ht eps.
specialize (Cdf t Ht eps).
simpl in Cdf.
destruct Cdf as (d,Cdf).
exists d.
intros v u Hv Hu.
now apply Cdf.
assert (Cdf' := uniform_continuity_2d_1d (fun u v => Derive (fun z => f z u) v) a b x Cdf'').
intros eps.
try clearbody Cdf'.
clear Cdf.
assert (H': 0 < eps / Rabs (b - a)).
apply Rmult_lt_0_compat.
apply cond_pos.
apply Rinv_0_lt_compat.
apply Rabs_pos_lt.
apply Rgt_not_eq.
now apply Rgt_minus.
move: (Cdf' (mkposreal _ H')) => {Cdf'} [d1 Cdf].
generalize (filter_and _ _ Df If).
move => {Df If} [d2 DIf].
exists (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2))) => /= y Hy.
assert (D1: ex_RInt (fun t => f y t) a b).
apply DIf.
apply Rlt_le_trans with (1 := Hy).
apply Rle_trans with (1 := Rmin_r _ _).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
assert (D2: ex_RInt (fun t => f x t) a b).
apply DIf.
apply ball_center.
rewrite -RInt_minus // -RInt_scal //.
assert (D3: ex_RInt (fun t => f y t - f x t) a b).
apply @ex_RInt_minus.
by apply D1.
by apply D2.
assert (D4: ex_RInt (fun t => (y - x) * Derive (fun u => f u t) x) a b) by now apply @ex_RInt_scal.
rewrite -RInt_minus //.
assert (D5: ex_RInt (fun t => f y t - f x t - (y - x) * Derive (fun u => f u t) x) a b) by now apply @ex_RInt_minus.
rewrite (RInt_Reals _ _ _ (ex_RInt_Reals_0 _ _ _ D5)).
assert (D6: ex_RInt (fun t => Rabs (f y t - f x t - (y - x) * Derive (fun u => f u t) x)) a b) by now apply ex_RInt_norm.
apply Rle_trans with (1 := RiemannInt_P17 _ (ex_RInt_Reals_0 _ _ _ D6) (Rlt_le _ _ H)).
refine (Rle_trans _ _ _ (RiemannInt_P19 _ (RiemannInt_P14 a b (eps / Rabs (b - a) * Rabs (y - x))) (Rlt_le _ _ H) _) _).
intros u Hu.
destruct (MVT_cor4 (fun t => f t u) (Derive (fun t => f t u)) x) with (eps := pos_div_2 d2) (b := y) as (z,Hz).
intros z Hz.
apply Derive_correct, DIf.
apply Rle_lt_trans with (1 := Hz).
apply: Rlt_eps2_eps.
apply cond_pos.
split ; now apply Rlt_le.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
rewrite (proj1 Hz).
rewrite Rmult_comm.
rewrite -Rmult_minus_distr_l Rabs_mult.
rewrite Rmult_comm.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rlt_le.
apply Cdf.
split ; now apply Rlt_le.
apply Rabs_le_between'.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le.
apply cond_pos.
split ; now apply Rlt_le.
apply Rabs_le_between'.
apply Rle_trans with (1 := proj2 Hz).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite RiemannInt_P15.
rewrite Rabs_pos_eq.
right.
change (norm (minus y x)) with (Rabs (y - x)).
field.
apply Rgt_not_eq.
now apply Rgt_minus.
apply Rge_le.
apply Rge_minus.
Admitted.

Lemma is_derive_RInt_param : forall f a b x, locally x (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) -> (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) -> locally x (fun y => ex_RInt (fun t => f y t) a b) -> is_derive (fun x => RInt (fun t => f x t) a b) x (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x H1 H2 H3.
apply is_derive_RInt_param_aux; try easy.
apply ex_RInt_Reals_1.
clear H1 H3.
wlog: a b H2 / a < b => H.
case (total_order_T a b).
intro Y; case Y.
now apply H.
intros Heq; rewrite Heq.
apply RiemannInt_P7.
intros Y.
apply RiemannInt_P1.
apply H.
intros; apply H2.
rewrite Rmin_comm Rmax_comm.
exact H0.
exact Y.
rewrite Rmin_left in H2.
2: now left.
rewrite Rmax_right in H2.
2: now left.
apply continuity_implies_RiemannInt.
now left.
intros y Hy eps Heps.
destruct (H2 _ Hy (mkposreal eps Heps)) as (d,Hd).
simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist; simpl.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
Admitted.

Lemma is_derive_RInt_param_bound_comp_aux1 : forall (f : R -> R -> R) (a : R -> R) (x : R), (exists eps:posreal, locally x (fun y : R => ex_RInt (fun t => f y t) (a x - eps) (a x + eps))) -> (exists eps:posreal, locally x (fun x0 : R => forall t : R, a x-eps <= t <= a x+eps -> ex_derive (fun u : R => f u t) x0)) -> (locally_2d (fun x' t => continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) -> continuity_2d_pt (fun u v : R => Derive (fun z : R => RInt (fun t : R => f z t) v (a x)) u) x (a x).
Proof.
intros f a x (d1,(d2,Ia)) (d3,(d4,Df)) Cdf e.
assert (J1:(continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x (a x))) by now apply locally_2d_singleton in Cdf.
destruct Cdf as (d5,Cdf).
destruct (J1 (mkposreal _ Rlt_0_1)) as (d6,Df1); simpl in Df1.
assert (J2: 0 < e / (Rabs (Derive (fun z : R => f z (a x)) x)+1)).
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
exists (mkposreal _ (Rmin_stable_in_posreal (mkposreal _ (Rmin_stable_in_posreal d1 (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d2) d3)))) (mkposreal _ (Rmin_stable_in_posreal (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d4) d5)) (mkposreal _ (Rmin_stable_in_posreal d6 (mkposreal _ J2))))))).
simpl; intros u v Hu Hv.
rewrite (Derive_ext (fun z : R => RInt (fun t : R => f z t) (a x) (a x)) (fun z => 0)).
2: intros t; exact: RInt_point.
replace (Derive (fun _ : R => 0) x) with 0%R.
2: apply sym_eq, Derive_const.
rewrite Rminus_0_r.
replace (Derive (fun z : R => RInt (fun t : R => f z t) v (a x)) u) with (RInt (fun z => Derive (fun u => f u z) u) v (a x)).
apply Rle_lt_trans with (Rabs (a x -v) * (Rabs (Derive (fun z : R => f z (a x)) x) +1)).
apply (norm_RInt_le_const_abs (fun z : R => Derive (fun u0 : R => f u0 z) u) v (a x)).
intros t Ht.
apply Rplus_le_reg_r with (-Rabs (Derive (fun z : R => f z (a x)) x)).
apply Rle_trans with (1:=Rabs_triang_inv _ _).
ring_simplify.
left; apply Df1.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply: RInt_correct.
apply: ex_RInt_continuous.
intros y Hy ; apply continuity_pt_filterlim.
intros eps Heps.
assert (Y1:(Rabs (u - x) < d5)).
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
assert (Y2:(Rabs (y - a x) < d5)).
apply Rle_lt_trans with (Rabs (v-a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
destruct (Cdf u y Y1 Y2 (mkposreal eps Heps)) as (d,Hd); simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
replace (a x -v) with (-(v - a x)) by ring; rewrite Rabs_Ropp.
apply Rlt_le_trans with ((e / (Rabs (Derive (fun z : R => f z (a x)) x) + 1)) * (Rabs (Derive (fun z : R => f z (a x)) x) + 1)).
apply Rmult_lt_compat_r.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
right; field.
apply sym_not_eq, Rlt_not_eq.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
apply sym_eq, is_derive_unique.
apply is_derive_RInt_param.
exists (pos_div_2 d4).
intros y Hy t Ht.
apply Df.
rewrite (double_var d4).
apply ball_triangle with u.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
by apply Hy.
apply (proj1 (Rabs_le_between' t (a x) d3)).
apply Rle_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
intros t Ht.
apply Cdf.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
exists (pos_div_2 d2).
intros y Hy.
apply (ex_RInt_inside (f y)) with (a x) d1.
apply Ia.
rewrite (double_var d2).
apply ball_triangle with u.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Hy.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
Admitted.

Lemma continuous_RInt (f : R -> V) (a b : R) (If : R -> R -> V) : locally (a,b) (fun z : R * R => is_RInt f (fst z) (snd z) (If (fst z) (snd z))) -> continuous (fun z : R * R => If (fst z) (snd z)) (a,b).
Proof.
intros HIf.
move: (locally_singleton _ _ HIf) => /= Hab.
apply continuous_ext_loc with (fun z : R * R => plus (If (fst z) b) (plus (opp (If a b)) (If a (snd z)))) ; simpl.
assert (Ha : locally (a,b) (fun z : R * R => is_RInt f a (snd z) (If a (snd z)))).
case: HIf => /= d HIf.
exists d => y /= Hy.
apply (HIf (a,(snd y))) ; split => //=.
by apply ball_center.
by apply Hy.
assert (Hb : locally (a,b) (fun z : R * R => is_RInt f (fst z) b (If (fst z) b))).
case: HIf => /= d HIf.
exists d => x /= Hx.
apply (HIf (fst x,b)) ; split => //=.
by apply Hx.
by apply ball_center.
generalize (filter_and _ _ HIf (filter_and _ _ Ha Hb)).
apply filter_imp => {HIf Ha Hb} /= x [HIf [Ha Hb]].
apply eq_close.
eapply filterlim_locally_close.
eapply is_RInt_Chasles.
by apply Hb.
eapply is_RInt_Chasles.
by apply is_RInt_swap, Hab.
by apply Ha.
by apply HIf.
eapply filterlim_comp_2, filterlim_plus ; simpl.
apply (continuous_comp (fun x => fst x) (fun x => If x b)) ; simpl.
apply continuous_fst.
eapply (continuous_RInt_2 f _ b).
case: HIf => /= d HIf.
exists d => x /= Hx.
apply (HIf (x,b)).
split => //=.
by apply ball_center.
eapply filterlim_comp_2, filterlim_plus ; simpl.
apply filterlim_const.
apply (continuous_comp (fun x => snd x) (fun x => If a x)) ; simpl.
apply continuous_snd.
eapply (continuous_RInt_1 f a b).
case: HIf => /= d HIf.
exists d => x /= Hx.
apply (HIf (a,x)).
split => //=.
by apply ball_center.

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

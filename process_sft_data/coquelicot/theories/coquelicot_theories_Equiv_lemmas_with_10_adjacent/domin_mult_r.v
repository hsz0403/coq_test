Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Hierarchy.
Definition is_domin {T} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} (F : (T -> Prop) -> Prop) (f : T -> U) (g : T -> V) := forall eps : posreal, F (fun x => norm (g x) <= eps * norm (f x)).
Definition is_equiv {T} {K : AbsRing} {V : NormedModule K} (F : (T -> Prop) -> Prop) (f g : T -> V) := is_domin F g (fun x => minus (g x) (f x)).
Section Equiv.
Context {T : Type} {K : AbsRing} {V : NormedModule K}.
End Equiv.
Section Domin.
Context {T : Type} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv}.
End Domin.
Section Equiv_VS.
Context {T : Type} {K : AbsRing} {V : NormedModule K}.
End Equiv_VS.
Section Domin_comp.
Context {T1 T2 : Type} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} (F : (T1 -> Prop) -> Prop) {FF : Filter F} (G : (T2 -> Prop) -> Prop) {FG : Filter G}.
End Domin_comp.

Lemma equiv_trans : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f g h : T -> V), is_equiv F f g -> is_equiv F g h -> is_equiv F f h.
Proof.
intros F FF f g h Hfg Hgh.
apply (fun c => domin_rw_l _ _ c Hgh).
intros eps.
apply equiv_sym in Hgh.
generalize (filter_and _ _ (Hfg (pos_div_2 eps)) (Hgh (pos_div_2 eps))) => {Hfg Hgh}.
apply filter_imp => x /= [Hfg Hgh].
replace (minus (h x) (f x)) with (plus (minus (g x) (f x)) (opp (minus (g x) (h x)))).
eapply Rle_trans.
1 : by apply @norm_triangle.
rewrite norm_opp (double_var eps) Rmult_plus_distr_r.
by apply Rplus_le_compat.
rewrite /minus opp_plus opp_opp plus_comm plus_assoc.
congr (plus _ (opp (f x))).
rewrite plus_comm plus_assoc plus_opp_r.
Admitted.

Lemma equiv_carac_0 : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> V), is_equiv F f g -> {o : T -> V | (forall x : T, f x = plus (g x) (o x)) /\ is_domin F g o }.
Proof.
intros F FF f g H.
exists (fun x => minus (f x) (g x)).
split.
intro x.
by rewrite /minus plus_comm -plus_assoc plus_opp_l plus_zero_r.
apply (domin_rw_l _ _ _ H).
Admitted.

Lemma equiv_carac_1 : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f g o : T -> V), (forall x, f x = plus (g x) (o x)) -> is_domin F g o -> is_equiv F f g.
Proof.
intros F FF f g o Ho Hgo.
intro eps ; move: (Hgo eps).
apply filter_imp => x.
replace (o x) with (minus (f x) (g x)).
congr (_ <= _).
by rewrite -norm_opp /minus opp_plus opp_opp plus_comm.
rewrite Ho.
rewrite /minus plus_comm plus_assoc plus_opp_l.
Admitted.

Lemma equiv_ext_loc {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> V) : F (fun x => f x = g x) -> is_equiv F f g.
Proof.
move => H eps.
move: H ; apply filter_imp.
move => x ->.
rewrite /minus plus_opp_r norm_zero.
apply Rmult_le_pos.
by apply Rlt_le, eps.
Admitted.

Lemma is_domin_le {F G} (f : T -> U) (g : T -> V) : is_domin F f g -> filter_le G F -> is_domin G f g.
Proof.
intros.
intros eps.
Admitted.

Lemma domin_scal_r : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (g : T -> V) (c : Kv), is_domin F f g -> is_domin F f (fun x => scal c (g x)).
Proof.
intros F FF f g c H.
case: (Req_dec (abs c) 0) => Hc.
move => eps /=.
apply filter_imp with (2 := filter_true) => x _.
eapply Rle_trans.
apply @norm_scal.
rewrite Hc Rmult_0_l.
apply Rmult_le_pos.
by apply Rlt_le, eps.
by apply norm_ge_0.
destruct (abs_ge_0 c) => //.
clear Hc ; rename H0 into Hc.
move => eps /=.
assert (He : 0 < eps / abs c).
apply Rdiv_lt_0_compat.
by apply eps.
by apply Hc.
move: (H (mkposreal _ He)) => /= {H}.
apply filter_imp => x H.
eapply Rle_trans.
apply @norm_scal.
rewrite Rmult_comm ; apply Rle_div_r.
by [].
apply Rle_trans with (1 := H).
apply Req_le ; rewrite /Rdiv ; ring.
Admitted.

Lemma domin_scal_l : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (g : T -> V) (c : Ku), (exists y, mult y c = one) -> is_domin F f g -> is_domin F (fun x => scal c (f x)) g.
Proof.
intros F FF f g c Hc H eps.
destruct Hc as [y Hc].
assert (0 < abs c).
apply Rnot_le_lt => H0.
destruct H0.
move: H0 ; by apply Rle_not_lt, abs_ge_0.
move: H0.
apply (Rmult_neq_0_reg (abs y)).
apply Rgt_not_eq.
eapply Rlt_le_trans, @abs_mult.
rewrite Hc abs_one ; by apply Rlt_0_1.
assert (0 < abs y).
apply Rmult_lt_reg_r with (abs c).
by [].
rewrite Rmult_0_l.
eapply Rlt_le_trans, @abs_mult.
rewrite Hc abs_one ; by apply Rlt_0_1.
assert (He : (0 < eps / abs y)).
apply Rdiv_lt_0_compat.
by apply eps.
by [].
move: (H (mkposreal _ He)) => /= {H}.
apply filter_imp => x Hx.
apply Rle_trans with (1 := Hx).
rewrite /Rdiv Rmult_assoc ; apply Rmult_le_compat_l.
by apply Rlt_le, eps.
rewrite -{1}(scal_one (f x)) -Hc -scal_assoc.
eapply Rle_trans.
apply Rmult_le_compat_l.
by apply Rlt_le, Rinv_0_lt_compat.
apply @norm_scal.
apply Req_le ; field.
Admitted.

Lemma domin_plus : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (g1 g2 : T -> V), is_domin F f g1 -> is_domin F f g2 -> is_domin F f (fun x => plus (g1 x) (g2 x)).
Proof.
intros F FF f g1 g2 Hg1 Hg2 eps.
generalize (filter_and _ _ (Hg1 (pos_div_2 eps)) (Hg2 (pos_div_2 eps))) => /= {Hg1 Hg2}.
apply filter_imp => x [Hg1 Hg2].
eapply Rle_trans.
apply @norm_triangle.
eapply Rle_trans.
apply Rplus_le_compat.
by apply Hg1.
by apply Hg2.
Admitted.

Lemma equiv_scal : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> V) (c : K), (exists y : K, mult y c = one) -> is_equiv F f g -> is_equiv F (fun x => scal c (f x)) (fun x => scal c (g x)).
Proof.
intros F FF f g c [y Hc] H.
apply domin_scal_l.
by exists y.
move => eps /=.
cut (F (fun x => norm (scal c (minus (g x) (f x))) <= eps * norm (g x))).
apply filter_imp => x.
now rewrite scal_distr_l scal_opp_r.
Admitted.

Lemma equiv_plus : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f o : T -> V), is_domin F f o -> is_equiv F (fun x => plus (f x) (o x)) f.
Proof.
intros F FF f o H eps.
move: (H eps) => {H}.
apply filter_imp => x Hx.
simpl.
Admitted.

Lemma domin_mult_l : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g h : T -> R), is_domin F f g -> is_domin F (fun x => h x * f x) (fun x => h x * g x).
Proof.
intros T F FF f g h H eps.
generalize (domin_mult_r f g h H eps).
apply filter_imp => x.
Admitted.

Lemma domin_mult : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f1 f2 g1 g2 : T -> R), is_domin F f1 g1 -> is_domin F f2 g2 -> is_domin F (fun x => f1 x * f2 x) (fun x => g1 x * g2 x).
Proof.
intros T F FF f1 f2 g1 g2 H1 H2 eps.
move: (H1 (mkposreal _ (sqrt_lt_R0 _ (cond_pos eps)))) (H2 (mkposreal _ (sqrt_lt_R0 _ (cond_pos eps)))) => {H1 H2} /= H1 H2.
generalize (filter_and _ _ H1 H2) => {H1 H2}.
apply filter_imp => x [H1 H2].
rewrite /norm /= /abs /= ?Rabs_mult.
rewrite -(sqrt_sqrt _ (Rlt_le _ _ (cond_pos eps))).
replace (sqrt eps * sqrt eps * (Rabs (f1 x) * Rabs (f2 x))) with ((sqrt eps * Rabs (f1 x))*(sqrt eps * Rabs (f2 x))) by ring.
apply Rmult_le_compat.
by apply Rabs_pos.
by apply Rabs_pos.
by apply H1.
Admitted.

Lemma domin_inv : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R), F (fun x => g x <> 0) -> is_domin F f g -> is_domin F (fun x => / g x) (fun x => / f x).
Proof.
intros T F FF f g Hg H eps.
have Hf : F (fun x => f x <> 0).
generalize (filter_and _ _ Hg (H (mkposreal _ Rlt_0_1))) => /=.
apply filter_imp => x {Hg H} [Hg H].
case: (Req_dec (f x) 0) => Hf.
rewrite /norm /= /abs /= Hf Rabs_R0 Rmult_0_r in H.
apply Rlt_not_le in H.
move => _ ; apply H.
by apply Rabs_pos_lt.
by [].
generalize (filter_and _ _ (H eps) (filter_and _ _ Hf Hg)) => {H Hf Hg}.
apply filter_imp => x [H [Hf Hg]].
rewrite /norm /= /abs /= ?Rabs_Rinv => //.
replace (/ Rabs (f x)) with (Rabs (g x) / (Rabs (f x) * Rabs (g x))) by (field ; split ; by apply Rabs_no_R0).
replace (eps * / Rabs (g x)) with (eps * Rabs (f x) / (Rabs (f x) * Rabs (g x))) by (field ; split ; by apply Rabs_no_R0).
apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat ; apply Rabs_pos_lt => //.
Admitted.

Lemma equiv_mult : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f1 f2 g1 g2 : T -> R), is_equiv F f1 g1 -> is_equiv F f2 g2 -> is_equiv F (fun x => f1 x * f2 x) (fun x => g1 x * g2 x).
Proof.
intros T F FF f1 f2 g1 g2 H1 H2.
case: (equiv_carac_0 _ _ H1) => {H1} o1 [H1 Ho1].
case: (equiv_carac_0 _ _ H2) => {H2} o2 [H2 Ho2].
apply equiv_carac_1 with (fun x => o1 x * g2 x + g1 x * o2 x + o1 x * o2 x).
move => x ; rewrite H1 H2 /plus /= ; ring.
repeat apply @domin_plus => //.
by apply domin_mult_r.
by apply domin_mult_l.
Admitted.

Lemma equiv_inv : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R), F (fun x => g x <> 0) -> is_equiv F f g -> is_equiv F (fun x => / f x) (fun x => / g x).
Proof.
intros T F FF f g Hg H.
have Hf : F (fun x => f x <> 0).
generalize (filter_and _ _ Hg (H (pos_div_2 (mkposreal _ Rlt_0_1)))) => /=.
apply filter_imp => x {Hg H} [Hg H].
case: (Req_dec (f x) 0) => Hf //.
rewrite /minus /plus /opp /= Hf Ropp_0 Rplus_0_r in H.
generalize (norm_ge_0 (g x)) (norm_eq_zero (g x)).
rewrite /zero /=.
lra.
apply equiv_sym in H.
move => eps.
generalize (filter_and _ _ (filter_and _ _ Hf Hg) (H eps)).
clear -FF.
apply filter_imp.
intros x [[Hf Hg] H].
rewrite /norm /= /abs /minus /plus /opp /=.
replace (/ g x + - / f x) with ((f x - g x) / (f x * g x)).
rewrite Rabs_div ?Rabs_Rinv ?Rabs_mult //.
apply Rle_div_l.
apply Rmult_lt_0_compat ; by apply Rabs_pos_lt.
field_simplify ; rewrite ?Rdiv_1.
by [].
by apply Rabs_no_R0.
by apply Rmult_integral_contrapositive_currified.
Admitted.

Lemma domin_comp (f : T2 -> U) (g : T2 -> V) (l : T1 -> T2) : filterlim l F G -> is_domin G f g -> is_domin F (fun t => f (l t)) (fun t => g (l t)).
Proof.
intros Hl Hg eps.
generalize (fun eps => Hl _ (Hg eps)) => {Hl Hg} /= Hl.
Admitted.

Lemma filterlim_equiv : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R) (l : Rbar), is_equiv F f g -> filterlim f F (Rbar_locally l) -> filterlim g F (Rbar_locally l).
Proof.
intros T F FF f g [l| |] Hfg Hf P [eps HP] ; apply equiv_sym in Hfg ; unfold filtermap.
-
assert (He: 0 < eps / 2 / (Rabs l + 1)).
apply Rdiv_lt_0_compat.
apply is_pos_div_2.
apply Rplus_le_lt_0_compat.
apply Rabs_pos.
apply Rlt_0_1.
pose ineqs (y : R) := Rabs (y - l) < eps/2 /\ Rabs y <= Rabs l + 1.
assert (Hl: Rbar_locally l ineqs).
assert (H: 0 < Rmin (eps / 2) 1).
apply Rmin_case.
apply is_pos_div_2.
apply Rlt_0_1.
exists (mkposreal _ H).
simpl.
intros x Hx.
split.
apply Rlt_le_trans with (1 := Hx).
apply Rmin_l.
apply Rabs_le_between'.
apply Rle_trans with (1 := Rabs_triang_inv2 _ _).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx).
apply Rmin_r.
generalize (filter_and _ (fun (x : T) => ineqs (f x)) (Hfg (mkposreal _ He)) (Hf _ Hl)).
apply filter_imp.
simpl.
intros x [H1 [H2 H3]].
apply HP.
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /=.
replace (g x + - l) with ((f x - l) + -(f x - g x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (eps / 2 + eps / 2 / (Rabs l + 1) * (Rabs l + 1)).
apply Rplus_lt_le_compat with (1 := H2).
rewrite Rabs_Ropp.
apply Rle_trans with (1 := H1).
apply Rmult_le_compat_l with (2 := H3).
now apply Rlt_le.
field.
apply Rgt_not_eq.
apply Rplus_le_lt_0_compat.
apply Rabs_pos.
apply Rlt_0_1.
-
pose ineq (y : R) := Rmax 0 (2 * eps) < y.
assert (Hl: Rbar_locally' p_infty ineq).
now exists (Rmax 0 (2 * eps)).
generalize (filter_and _ (fun (x : T) => ineq (f x)) (Hfg (mkposreal _ pos_half_prf)) (Hf _ Hl)).
apply filter_imp.
simpl.
intros x [H1 H2].
apply HP.
apply Rabs_le_between' in H1.
generalize (Rplus_le_compat_l (- /2 * Rabs (f x)) _ _ (proj2 H1)).
rewrite /norm /= /abs /=.
replace (- / 2 * Rabs (f x) + (g x + / 2 * Rabs (f x))) with (g x) by ring.
apply Rlt_le_trans.
rewrite Rabs_pos_eq.
apply Rmult_lt_reg_l with (1 := Rlt_R0_R2).
replace (2 * (- / 2 * f x + f x)) with (f x) by field.
apply Rle_lt_trans with (2 := H2).
apply Rmax_r.
apply Rlt_le.
apply Rle_lt_trans with (2 := H2).
apply Rmax_l.
-
pose ineq (y : R) := y < Rmin 0 (2 * eps).
assert (Hl: Rbar_locally' m_infty ineq).
now exists (Rmin 0 (2 * eps)).
generalize (filter_and _ (fun (x : T) => ineq (f x)) (Hfg (mkposreal _ pos_half_prf)) (Hf _ Hl)).
apply filter_imp.
simpl.
intros x [H1 H2].
apply HP.
apply Rabs_le_between' in H1.
generalize (Rplus_le_compat_l (/2 * Rabs (f x)) _ _ (proj1 H1)).
rewrite /norm /= /abs /=.
replace (/ 2 * Rabs (f x) + (g x - / 2 * Rabs (f x))) with (g x) by ring.
intros H.
apply Rle_lt_trans with (1 := H).
rewrite Rabs_left.
apply Rmult_lt_reg_l with (1 := Rlt_R0_R2).
replace (2 * (/ 2 * - f x + f x)) with (f x) by field.
apply Rlt_le_trans with (1 := H2).
apply Rmin_r.
apply Rlt_le_trans with (1 := H2).
Admitted.

Lemma domin_mult_r : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g h : T -> R), is_domin F f g -> is_domin F (fun x => f x * h x) (fun x => g x * h x).
Proof.
intros T F FF f g h H eps.
move: (H eps) => {H}.
apply filter_imp => x H1.
rewrite /norm /= /abs /= ?Rabs_mult.
rewrite -Rmult_assoc.
apply Rmult_le_compat_r.
by apply Rabs_pos.
by apply H1.

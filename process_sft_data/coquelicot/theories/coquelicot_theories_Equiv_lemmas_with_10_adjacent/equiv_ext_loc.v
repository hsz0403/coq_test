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

Lemma domin_antisym {T} {K : AbsRing} {V : NormedModule K} : forall {F : (T -> Prop) -> Prop} {FF : ProperFilter F} (f : T -> V), F (fun x => norm (f x) <> 0) -> ~ is_domin F f f.
Proof.
intros F FF f Hf H.
move: (H (pos_div_2 (mkposreal _ Rlt_0_1))) => {H} /= H.
apply filter_const.
generalize (filter_and _ _ H Hf) => {H Hf}.
apply filter_imp.
intros x [H1 H2].
generalize (norm_ge_0 (f x)).
Admitted.

Lemma domin_trans {T} {Ku Kv Kw : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} {W : NormedModule Kw} : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (g : T -> V) (h : T -> W), is_domin F f g -> is_domin F g h -> is_domin F f h.
Proof.
intros F FF f g h Hfg Hgh eps.
apply (filter_imp (fun x => (norm (h x) <= sqrt eps * norm (g x)) /\ (norm (g x) <= sqrt eps * norm (f x)))).
intros x [H0 H1].
apply Rle_trans with (1 := H0).
rewrite -{2}(sqrt_sqrt eps).
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
by apply sqrt_pos.
apply H1.
by apply Rlt_le, eps.
apply filter_and.
by apply (Hgh (mkposreal (sqrt eps) (sqrt_lt_R0 _ (cond_pos eps)))).
Admitted.

Lemma equiv_le_2 {T} {K : AbsRing} {V : NormedModule K} F {FF : Filter F} (f g : T -> V) : is_equiv F f g -> F (fun x => norm (g x) <= 2 * norm (f x) /\ norm (f x) <= 2 * norm (g x)).
Admitted.

Lemma domin_rw_l {T} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f1 f2 : T -> U) (g : T -> V), is_equiv F f1 f2 -> is_domin F f1 g -> is_domin F f2 g.
Proof.
intros F FF f1 f2 g Hf Hg eps.
assert (F (fun x => norm (f1 x) <= 2 * norm (f2 x))).
eapply filter_imp.
2: apply (equiv_le_2 _ _ _ Hf).
move => /= x Hx.
by apply Hx.
clear Hf ; rename H into Hf.
specialize (Hg (pos_div_2 eps)).
generalize (filter_and _ _ Hf Hg) ; clear -FF.
apply filter_imp => x /= [Hf Hg].
apply Rle_trans with (1 := Hg).
rewrite /Rdiv Rmult_assoc.
apply Rmult_le_compat_l.
by apply Rlt_le, eps.
rewrite Rmult_comm Rle_div_l.
by rewrite Rmult_comm.
Admitted.

Lemma domin_rw_r {T} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (g1 g2 : T -> V), is_equiv F g1 g2 -> is_domin F f g1 -> is_domin F f g2.
Proof.
intros F FF f g1 g2 Hg Hf eps.
assert (F (fun x => norm (g2 x) <= 2 * norm (g1 x))).
eapply filter_imp.
2: apply (equiv_le_2 _ _ _ Hg).
move => /= x Hx.
by apply Hx.
clear Hg ; rename H into Hg.
specialize (Hf (pos_div_2 eps)).
generalize (filter_and _ _ Hf Hg) ; clear -FF.
apply filter_imp => x /= [Hf Hg].
apply Rle_trans with (1 := Hg).
rewrite Rmult_comm Rle_div_r.
apply Rle_trans with (1 := Hf).
right ; rewrite /Rdiv ; ring.
Admitted.

Lemma equiv_refl : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> V), is_equiv F f f.
Proof.
intros F FF f eps.
apply: filter_forall => x.
rewrite /minus plus_opp_r norm_zero.
apply Rmult_le_pos.
by apply Rlt_le, eps.
Admitted.

Lemma equiv_sym : forall {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> V), is_equiv F f g -> is_equiv F g f.
Proof.
intros F FF f g H eps.
assert (H0 := equiv_le_2 _ _ _ H).
specialize (H (pos_div_2 eps)).
generalize (filter_and _ _ H H0) ; apply filter_imp ; clear => x [H [H0 H1]].
rewrite -norm_opp /minus opp_plus opp_opp plus_comm.
apply Rle_trans with (1 := H) ; simpl.
eapply Rle_trans.
apply Rmult_le_compat_l.
by apply Rlt_le, is_pos_div_2.
by apply H0.
Admitted.

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

Lemma domin_mult_r : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g h : T -> R), is_domin F f g -> is_domin F (fun x => f x * h x) (fun x => g x * h x).
Proof.
intros T F FF f g h H eps.
move: (H eps) => {H}.
apply filter_imp => x H1.
rewrite /norm /= /abs /= ?Rabs_mult.
rewrite -Rmult_assoc.
apply Rmult_le_compat_r.
by apply Rabs_pos.
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

Lemma equiv_ext_loc {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> V) : F (fun x => f x = g x) -> is_equiv F f g.
Proof.
move => H eps.
move: H ; apply filter_imp.
move => x ->.
rewrite /minus plus_opp_r norm_zero.
apply Rmult_le_pos.
by apply Rlt_le, eps.
by apply norm_ge_0.

Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Rbar Hierarchy RInt Lim_seq Continuity Derive.
Require Import Rcomplements RInt_analysis.
Open Scope R_scope.
Section is_RInt_gen.
Context {V : NormedModule R_AbsRing}.
Definition is_RInt_gen (f : R -> V) (Fa Fb : (R -> Prop) -> Prop) (l : V) := filterlimi (fun ab => is_RInt f (fst ab) (snd ab)) (filter_prod Fa Fb) (locally l).
Definition ex_RInt_gen (f : R -> V) (Fa Fb : (R -> Prop) -> Prop) := exists l : V, is_RInt_gen f Fa Fb l.
Definition is_RInt_gen_at_point f a b l : is_RInt_gen f (at_point a) (at_point b) l <-> is_RInt f a b l.
Proof.
split.
-
intros H P HP.
apply locally_locally in HP.
specialize (H _ HP).
destruct H as [Q R Qa Rb H].
destruct (H a b Qa Rb) as [y [Hy1 Hy2]].
now apply Hy1.
-
intros Hl P HP.
exists (fun x => x = a) (fun x => x = b) ; try easy.
intros x y -> ->.
exists l.
apply (conj Hl).
exact: locally_singleton.
End is_RInt_gen.
Section RInt_gen.
Context {V : CompleteNormedModule R_AbsRing}.
Definition RInt_gen (f : R -> V) (a b : (R -> Prop) -> Prop) := iota (is_RInt_gen f a b).
End RInt_gen.
Section Complements_RInt_gen.
Context {V : CompleteNormedModule R_AbsRing}.
End Complements_RInt_gen.

Lemma is_RInt_gen_swap {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) : is_RInt_gen f Fb Fa l -> is_RInt_gen f Fa Fb (opp l).
Proof.
intros Hf P HP.
specialize (Hf (fun y => P (opp y))).
destruct Hf as [Q R HQ HR H].
exact: filterlim_opp.
apply: Filter_prod HR HQ _ => a b Ha Hb.
specialize (H b a Hb Ha).
destruct H as [y [Hy1 Hy2]].
exists (opp y).
split.
exact: is_RInt_swap.
Admitted.

Lemma is_RInt_gen_Chasles {Fa Fc : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFc : Filter Fc} (f : R -> V) (b : R) (l1 l2 : V) : is_RInt_gen f Fa (at_point b) l1 -> is_RInt_gen f (at_point b) Fc l2 -> is_RInt_gen f Fa Fc (plus l1 l2).
Proof.
intros Hab Hbc P HP.
specialize (filterlim_plus _ _ P HP).
intros [Q R HQ HR H].
specialize (Hab Q HQ).
specialize (Hbc R HR).
destruct Hab as [Qa Ra HQa HRa Hab].
destruct Hbc as [Qc Rc HQc HRc Hbc].
apply: Filter_prod HQa HRc _.
intros a c Ha Hc.
specialize (Hab _ _ Ha HRa).
specialize (Hbc _ _ HQc Hc).
destruct Hab as [ya [Hya1 Hya2]].
destruct Hbc as [yc [Hyc1 Hyc2]].
exists (plus ya yc).
split.
apply: is_RInt_Chasles Hya1 Hyc1.
Admitted.

Lemma is_RInt_gen_scal {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (k : R) (l : V) : is_RInt_gen f Fa Fb l -> is_RInt_gen (fun y => scal k (f y)) Fa Fb (scal k l).
Proof.
intros H P HP.
move /filterlim_scal_r in HP.
specialize (H _ HP).
unfold filtermapi in H |- *.
apply: filter_imp H.
move => [a b] /= [y [Hy1 Hy2]].
exists (scal k y).
apply: conj Hy2.
Admitted.

Lemma is_RInt_gen_opp {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) : is_RInt_gen f Fa Fb l -> is_RInt_gen (fun y => opp (f y)) Fa Fb (opp l).
Proof.
intros H P HP.
move /filterlim_opp in HP.
specialize (H _ HP).
unfold filtermapi in H |- *.
apply: filter_imp H.
move => [a b] /= [y [Hy1 Hy2]].
exists (opp y).
apply: conj Hy2.
Admitted.

Lemma is_RInt_gen_plus {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (lf lg : V) : is_RInt_gen f Fa Fb lf -> is_RInt_gen g Fa Fb lg -> is_RInt_gen (fun y => plus (f y) (g y)) Fa Fb (plus lf lg).
Proof.
intros Hf Hg P HP.
move /filterlim_plus in HP.
destruct HP as [Q R HQ HR H].
specialize (Hf _ HQ).
specialize (Hg _ HR).
unfold filtermapi in Hf, Hg |- *.
apply: filter_imp (filter_and _ _ Hf Hg).
move => [a b] /= [[If [HIf1 HIf2]] [Ig [HIg1 HIg2]]].
exists (plus If Ig).
apply: conj (H _ _ HIf2 HIg2).
Admitted.

Lemma is_RInt_gen_minus {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (lf lg : V) : is_RInt_gen f Fa Fb lf -> is_RInt_gen g Fa Fb lg -> is_RInt_gen (fun y => minus (f y) (g y)) Fa Fb (minus lf lg).
Proof.
intros Hf Hg.
apply: is_RInt_gen_plus Hf _.
Admitted.

Lemma is_RInt_gen_unique {Fa Fb : (R -> Prop) -> Prop} {FFa : ProperFilter' Fa} {FFb : ProperFilter' Fb} (f : R -> V) (l : V) : is_RInt_gen f Fa Fb l -> RInt_gen f Fa Fb = l.
Proof.
apply iota_filterlimi_locally.
apply filter_forall.
intros [a b] y1 u2 H1 H2.
rewrite -(is_RInt_unique _ _ _ _ H1).
Admitted.

Lemma RInt_gen_correct {Fa Fb : (R -> Prop) -> Prop} {FFa : ProperFilter' Fa} {FFb : ProperFilter' Fb} (f : R -> V) : ex_RInt_gen f Fa Fb -> is_RInt_gen f Fa Fb (RInt_gen f Fa Fb).
Proof.
intros [If HIf].
Admitted.

Lemma RInt_gen_norm {Fa Fb : (R -> Prop) -> Prop} {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f : R -> V) (g : R -> R) (lf : V) (lg : R) : filter_prod Fa Fb (fun ab => fst ab <= snd ab) -> filter_prod Fa Fb (fun ab => forall x, fst ab <= x <= snd ab -> norm (f x) <= g x) -> is_RInt_gen f Fa Fb lf -> is_RInt_gen g Fa Fb lg -> norm lf <= lg.
Proof.
intros Hab Hle Hf Hg.
apply (filterlim_le (F := filter_prod Fa Fb) (fun ab => norm (RInt f (fst ab) (snd ab))) (fun ab => RInt g (fst ab) (snd ab)) (norm lf) lg).
-
specialize (Hf _ (locally_ball lf (mkposreal _ Rlt_0_1))).
specialize (Hg _ (locally_ball lg (mkposreal _ Rlt_0_1))).
unfold filtermapi in Hf, Hg.
apply: filter_imp (filter_and _ _ (filter_and _ _ Hf Hg) (filter_and _ _ Hab Hle)) => {Hf Hg Hab Hle}.
move => [a b] /= [[[If [Hf1 Hf2]] [Ig [Hg1 Hg2]]] [H H']].
apply: norm_RInt_le H H' _ _.
apply: RInt_correct.
now exists If.
apply: RInt_correct.
now exists Ig.
-
eapply filterlim_comp, filterlim_norm.
intros P HP.
specialize (Hf P HP).
unfold filtermapi, filtermap in Hf |- *.
apply: filter_imp Hf.
move => [a b] /= [y [Hy1 Hy2]].
now rewrite (is_RInt_unique _ a b y Hy1).
-
intros P HP.
specialize (Hg P HP).
unfold filtermapi, filtermap in Hg |- *.
apply: filter_imp Hg.
move => [a b] /= [y [Hy1 Hy2]].
Admitted.

Lemma RInt_gen_ext {Fa Fb : (R -> Prop) -> Prop} {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f g : R -> V) : filter_prod Fa Fb (fun ab => forall x, Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) -> f x = g x) -> ex_RInt_gen f Fa Fb -> RInt_gen f Fa Fb = RInt_gen g Fa Fb.
Proof.
move => Heq [I HI].
rewrite (is_RInt_gen_unique f I HI); symmetry.
apply is_RInt_gen_unique.
Admitted.

Lemma is_RInt_gen_Derive {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> R) (la lb : R) : filter_prod Fa Fb (fun ab => forall x : R, Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) -> ex_derive f x) -> filter_prod Fa Fb (fun ab => forall x : R, Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) -> continuous (Derive f) x) -> filterlim f Fa (locally la) -> filterlim f Fb (locally lb) -> is_RInt_gen (Derive f) Fa Fb (lb - la).
Proof.
intros Df Cf Lfa Lfb P HP.
assert (HP': filter_prod Fa Fb (fun ab => P (f (snd ab) - f (fst ab)))).
unfold Rminus.
eapply filterlim_comp_2.
eapply filterlim_comp, Lfb.
by apply filterlim_snd.
eapply filterlim_comp, @filterlim_opp.
eapply filterlim_comp, Lfa.
by apply filterlim_fst.
exact: (filterlim_plus lb (- la)).
exact HP.
apply: filter_imp (filter_and _ _ (filter_and _ _ Df Cf) HP').
move => [a b] /= {Df Cf HP HP'} [[Df Cf] HP].
eexists.
apply: conj HP.
apply: is_RInt_derive => x Hx.
now apply Derive_correct, Df.
Admitted.

Lemma ex_RInt_gen_at_point f a b : @ex_RInt_gen V f (at_point a) (at_point b) <-> ex_RInt f a b.
Proof.
split; case => I.
rewrite is_RInt_gen_at_point => HI.
by exists I.
rewrite -is_RInt_gen_at_point => HI.
Admitted.

Lemma RInt_gen_at_point f a b : ex_RInt f a b -> @RInt_gen V f (at_point a) (at_point b) = RInt f a b.
Proof.
move => Hfint.
apply is_RInt_gen_unique.
apply is_RInt_gen_at_point.
Admitted.

Lemma RInt_gen_ext_eq {Fa Fb : (R -> Prop) -> Prop} {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f g : R -> V): (forall x, f x = g x) -> ex_RInt_gen f Fa Fb -> RInt_gen f Fa Fb = RInt_gen g Fa Fb.
Proof.
move => Heq.
apply: (RInt_gen_ext f g).
exact: filter_forall => bnds x _.

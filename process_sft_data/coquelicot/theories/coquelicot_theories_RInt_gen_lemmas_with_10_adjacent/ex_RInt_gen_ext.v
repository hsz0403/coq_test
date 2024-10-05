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
Admitted.

Lemma is_RInt_gen_ext {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (l : V) : filter_prod Fa Fb (fun ab => forall x, Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) -> f x = g x) -> is_RInt_gen f Fa Fb l -> is_RInt_gen g Fa Fb l.
Proof.
intros Heq.
apply: filterlimi_ext_loc.
apply: filter_imp Heq.
intros [a b] Heq y.
split.
now apply is_RInt_ext.
apply is_RInt_ext.
intros x Hx.
Admitted.

Lemma ex_RInt_gen_ext_eq {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) : (forall x, f x = g x) -> ex_RInt_gen f Fa Fb -> ex_RInt_gen g Fa Fb.
Proof.
move => Heq.
apply: ex_RInt_gen_ext.
Admitted.

Lemma is_RInt_gen_point (f : R -> V) (a : R) : is_RInt_gen f (at_point a) (at_point a) zero.
Proof.
apply is_RInt_gen_at_point.
Admitted.

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

Lemma ex_RInt_gen_ext {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) : filter_prod Fa Fb (fun ab => forall x, Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) -> f x = g x) -> ex_RInt_gen f Fa Fb -> ex_RInt_gen g Fa Fb.
Proof.
move => Heq.
case => I HI.
exists I.
exact: (is_RInt_gen_ext f g).

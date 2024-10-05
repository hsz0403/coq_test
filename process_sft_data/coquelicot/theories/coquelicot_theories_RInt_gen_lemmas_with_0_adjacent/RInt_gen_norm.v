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
now rewrite (is_RInt_unique _ a b y Hy1).

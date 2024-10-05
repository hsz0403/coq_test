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
now apply H.

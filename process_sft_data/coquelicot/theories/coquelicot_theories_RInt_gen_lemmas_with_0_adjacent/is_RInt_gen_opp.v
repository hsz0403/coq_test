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
exact: is_RInt_opp.

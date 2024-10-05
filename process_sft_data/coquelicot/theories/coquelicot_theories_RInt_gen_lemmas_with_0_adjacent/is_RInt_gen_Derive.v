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
exact: Cf.

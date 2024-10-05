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

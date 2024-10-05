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
by apply plus_zero_r.

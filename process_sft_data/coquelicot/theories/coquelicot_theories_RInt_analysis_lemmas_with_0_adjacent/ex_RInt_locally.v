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

Lemma ex_RInt_locally {V : CompleteNormedModule R_AbsRing} (f : R -> V) (a b : R) : ex_RInt f a b -> (exists eps : posreal, ex_RInt f (a - eps) (a + eps)) -> (exists eps : posreal, ex_RInt f (b - eps) (b + eps)) -> locally (a,b) (fun z : R * R => ex_RInt f (fst z) (snd z)).
Proof.
intros Hf (ea,Hea) (eb,Heb).
exists (mkposreal _ (Rmin_stable_in_posreal ea eb)) => [[a' b'] [Ha' Hb']] ; simpl in *.
apply ex_RInt_Chasles with (a - ea).
eapply ex_RInt_swap, ex_RInt_Chasles_1 ; try eassumption.
apply Rabs_le_between'.
eapply Rlt_le, Rlt_le_trans, Rmin_l.
by apply Ha'.
apply ex_RInt_Chasles with a.
eapply ex_RInt_Chasles_1 ; try eassumption.
apply Rabs_le_between'.
rewrite Rminus_eq_0 Rabs_R0.
by apply Rlt_le, ea.
apply ex_RInt_Chasles with b => //.
apply ex_RInt_Chasles with (b - eb).
eapply ex_RInt_swap, ex_RInt_Chasles_1; try eassumption.
apply Rabs_le_between'.
rewrite Rminus_eq_0 Rabs_R0.
by apply Rlt_le, eb.
eapply ex_RInt_Chasles_1 ; try eassumption.
apply Rabs_le_between'.
eapply Rlt_le, Rlt_le_trans, Rmin_r.
by apply Hb'.

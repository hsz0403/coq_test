From Undecidability.L.Computability Require Export Scott Acceptability.
Import Undecidability.L.Prelim.ARS.ARSNotations.
Import L_Notations.
Definition self_diverging (s : term) := ~ pi s s.
Definition self_diverging_comb := conj self_diverging proc.
Goal ~ ldec (fun s => proc s /\ forall t, pi s t).
Proof.
eapply Rice.
-
firstorder.
-
intuition;now apply H1.
-
exists (lam Omega).
split.
Lproc.
intros [_ A].
eapply lamOmega; eauto.
-
exists (lam I).
repeat split;try Lproc.
intros t; eexists; split; [|eexists;reflexivity].
now Lsimpl.
Grab Existential Variables.
repeat econstructor.
Goal ~ lacc (fun s => proc s /\ exists t, ~ pi s t).
Proof.
eapply Rice1.
-
firstorder.
-
intros s t cls_t [cls_s [t0 H]] He.
split; eauto.
exists t0.
rewrite <- He.
eassumption.
-
exists (lam I).
split.
Lproc.
intros [_ [? H]].
eapply H.
eexists;split;[|eexists;reflexivity].
now Lsimpl.
-
exists (lam Omega).
repeat split;try Lproc.
exists I.
eapply lamOmega.
-
split.
Lproc.
exists I.
eapply lamOmega.

Lemma Rice1 (M : term -> Prop) : (M <=1 proc) -> (forall (s t : term), proc t -> M s -> (forall u, pi s u <-> pi t u) -> M t) -> (exists p, proc p /\ ~ M p) -> (exists p, proc p /\ M p) -> M (lam Omega) -> ~ lacc M.
Proof with eauto; try now intuition.
intros M_proc M_cl_equiv [t2 [cls_t2 nMt2]] [t1 [cls_t1 nMt1]] MLO [u [[cls_u lam_u] Hu]].
eapply (self_div_comb).
destruct (dec_lacc ldec_proc) as [c [[cls_c lam_c] Hc]].
pose (v := lam ( u ((ext lam) ((ext app) (enc (lam (t2 #1))) ((ext app) #0 ((ext (enc(X:= term))) #0)))))).
pose (v' := acc_conj c v).
assert (proc v).
subst v;unfold acc_conj;Lproc.
assert (proc v').
subst v';unfold acc_conj;Lproc.
exists v'; split.
Lproc.
intros s.
pose (vs := lam ((lam (t2 #1)) (s (enc s)))).
symmetry.
transitivity (pi v s /\ proc s).
{
unfold v'.
rewrite acc_conj_correct;try Lproc.
rewrite <- Hc.
tauto.
}
unfold self_diverging_comb, conj.
transitivity (pi u vs /\ proc s).
{
split; intros [R cls_s];(split;[|Lproc]).
-
revert R.
eapply converges_proper.
symmetry.
subst v.
now Lsimpl.
-
revert R.
eapply converges_proper.
subst v.
now Lsimpl.
}
transitivity (M vs /\ proc s).
split; intros [? ?]; intuition; try (now rewrite Hu).
{
split.
-
intros [Mvs cls_s]; intuition.
intros [w [Hw lw]].
assert (forall t, pi vs t <-> pi t2 t).
{
intros t.
eapply converges_proper.
assert (closed w).
eapply (equiv_lambda lw) in Hw.
eapply closed_star.
exact Hw.
Lproc.
subst vs.
Lsimpl_old.
rewrite Hw.
now Lsimpl.
}
eapply nMt2.
eapply M_cl_equiv; eassumption.
-
intros [npi_s_s cls_s]; intuition.
assert (forall t, pi (lam Omega) t <-> pi vs t).
{
intros t; split; intros H'.
-
exfalso.
destruct H' as [w [Hw lw]].
inv lw.
eapply Omega_diverges.
rewrite <- Hw.
symmetry.
clear Hw.
now redStep.
-
exfalso.
eapply npi_s_s.
assert (A: converges (lam ( t2 (enc t)) (s (enc s)))).
revert H'.
eapply converges_proper.
symmetry.
unfold vs.
now Lsimpl_old.
eapply app_converges in A.
firstorder.
}
subst vs.
eapply M_cl_equiv; try Lproc;try eassumption.
}

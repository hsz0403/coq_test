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

Lemma Rice2 (M : term -> Prop) : (M <=1 proc) -> (forall (s t : term), proc t -> M s -> (forall u, pi s u <-> pi t u) -> M t) -> (exists p, proc p /\ ~ M p) -> (exists p, proc p /\ M p) -> ~ M (lam Omega) -> ~ lacc (complement M).
Proof.
intros M_cls M_cl_equiv [t2 [cls_t2 nMt2]] [t1 [cls_t1 nMt1]] nMLO decM.
destruct decM as [u [[cls_u lam_u] Hu]].
unfold complement in Hu.
eapply (self_div_comb).
destruct (dec_lacc ldec_proc) as [c [[cls_c lam_c] Hc]].
pose (v := lam ( u ((ext lam) ((ext app) (enc (lam (t1 #1))) ((ext app) #0 ((ext (enc (X:=term))) #0)))))).
pose (v' := acc_conj c v).
exists v'; split.
subst v' v.
unfold acc_conj.
Lproc.
intros s.
pose (vs := lam ((lam (t1 #1)) (s (enc s)))).
assert (cv:closed v) by (subst v; Lproc).
symmetry.
transitivity (pi v s /\ proc s).
{
unfold v'.
rewrite acc_conj_correct;try Lproc.
intuition ; now apply Hc.
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
transitivity (~ M vs /\ proc s).
{
split; intros [? ?]; try (rewrite Hu); intuition; firstorder.
}
{
split.
-
intros [Mvs cls_s]; intuition.
intros [w [Hw lw]].
assert (forall t, pi t1 t <-> pi vs t).
{
intros t.
symmetry.
assert (closed w).
eapply closed_star.
eapply equiv_lambda;eauto.
Lproc.
eapply converges_proper.
transitivity (lam ( t1 (enc t)) (s (enc s))).
unfold vs.
now Lsimpl_old.
rewrite Hw.
now Lsimpl.
}
eapply Mvs.
eapply M_cl_equiv;try subst vs; try Lproc; try eassumption.
-
intros [npi_s_s cls_s]; intuition.
assert (forall t, pi (lam Omega) t <-> pi vs t).
{
intros t; split; intros A.
-
exfalso.
destruct A as [w [Hw lw]].
inv lw.
eapply Omega_diverges.
rewrite <- Hw.
symmetry.
clear Hw.
now LsimplRed.
-
exfalso.
eapply npi_s_s.
assert (B: converges (lam ( t1 (enc t)) (s (enc s)))).
revert A.
eapply converges_proper.
symmetry.
unfold vs.
Lsimpl_old.
eapply app_converges in B.
firstorder.
}
eapply nMLO.
eapply M_cl_equiv; try (symmetry); eauto.
Lproc.
}

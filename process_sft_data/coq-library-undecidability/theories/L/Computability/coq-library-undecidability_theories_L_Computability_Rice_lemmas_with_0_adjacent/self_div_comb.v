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

Lemma self_div_comb : ~ lacc self_diverging_comb.
Proof.
intros [u [[cls_u lam_u] H]].
unfold self_diverging_comb in H.
unfold conj in H.
specialize (H u).
unfold self_diverging in H.
destruct H.
unfold proc in *.
tauto.

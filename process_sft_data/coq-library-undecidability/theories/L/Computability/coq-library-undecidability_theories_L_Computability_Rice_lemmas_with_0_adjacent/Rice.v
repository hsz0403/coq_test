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

Theorem Rice (M : term -> Prop) : (M <=1 proc) -> (forall (s t : term), proc t -> M s -> (forall u, pi s u <-> pi t u) -> M t) -> (exists p, proc p /\ ~ M p) -> (exists p, proc p /\ M p) -> ~ ldec M.
Proof.
intros.
intros A.
assert (B : ldec M) by eassumption.
destruct A as [u [proc_u Hu]].
destruct (Hu (lam Omega)) as [[] [eq m]].
-
eapply Rice1; try eassumption.
apply dec_lacc.
exists u; tauto.
-
eapply Rice2; try eassumption.
apply dec_lacc.
apply ldec_complement.
exists u; tauto.

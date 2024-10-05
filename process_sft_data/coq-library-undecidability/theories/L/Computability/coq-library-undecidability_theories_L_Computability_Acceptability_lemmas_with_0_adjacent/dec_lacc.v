From Undecidability.L Require Export LTerm Por Decidability Lbeta_nonrefl.
Import L_Notations.
Definition pi (s t:term) := converges (s (ext t)).
Definition lacc (P : term -> Prop) := exists u, proc u /\ forall t, P t <-> pi u t.
Goal forall s1 s2 t, s1 == s2 -> (pi s1 t <-> pi s2 t).
Proof.
intros s1 s2 t H; intuition; unfold pi; [now rewrite <- H | now rewrite H].
Definition acc_conj (p q : term) := lam ((lam (q #1)) (p #0) ).
Hint Unfold acc_conj : cbv.

Lemma dec_lacc M : ldec M -> lacc M.
Proof.
intros [u [[cls_u lam_u] dec_u_M]].
exists (lam (u #0 I (lam Omega) I)); split.
Lproc.
+
intros t.
specialize (dec_u_M t).
split; intros H; destruct dec_u_M; try tauto.
*
destruct H0 as [u_true ?].
eexists;split;[|eexists;reflexivity].
redSteps.
rewrite u_true.
destruct x.
now Lsimpl.
tauto.
*
destruct H0.
destruct x.
tauto.
assert ((lam ((((u #0) I) (lam Omega)) I)) (enc t) == Omega).
clear H.
LsimplRed.
rewrite H0.
Lrewrite.
now Lsimpl_old.
destruct H as [H [? []]].
subst H.
rewrite H2 in H3.
destruct (Omega_diverges H3).

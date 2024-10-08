From Undecidability.L Require Export Functions.Subst Computability.Seval Computability.MuRec Datatypes.LOptions.
Instance term_eva : computable eva.
Proof.
extract.
Definition doesHaltIn := fun u n => match eva n u with None => false | _ => true end.
Instance term_doesHaltIn : computable doesHaltIn.
Proof.
extract.
Section hoas.
Import HOAS_Notations.
Definition Eval :term := Eval cbn in convert(λ u, !!(ext eva) (!!mu (λ n, !!(ext doesHaltIn) u n)) u !!I !!I).
End hoas.
Import L_Notations.

Instance term_doesHaltIn : computable doesHaltIn.
Proof.
Admitted.

Lemma Eval_correct (s v:term) : lambda v -> (Eval (ext s) == v <-> exists (n:nat) (v':term), (ext eva) (ext n) (ext s) == ext (Some v') /\ v = ext v' /\ lambda v').
Proof.
intros lv.
unfold Eval.
split.
-
intros H.
LsimplHypo.
evar (c:term).
assert (C:converges c).
exists v.
split.
exact H.
Lproc.
subst c.
apply app_converges in C as [C _].
apply app_converges in C as [C _].
apply app_converges in C as [C _].
apply app_converges in C as [_ C].
destruct C as [w [R lw]].
rewrite R in H.
apply mu_sound in R as [n [ eq [R _]]];try Lproc.
+
subst w.
LsimplHypo.
Lrewrite in H.
Lrewrite in R.
apply enc_extinj in R.
unfold doesHaltIn in R.
destruct (eva n) eqn:eq.
*
exists n,t.
split.
Lsimpl.
now rewrite eq.
split.
apply unique_normal_forms;[Lproc..|].
rewrite <- H.
unfold I.
clear H.
now Lsimpl.
eapply eva_lam.
eauto.
*
congruence.
+
intros.
eexists.
Lsimpl.
reflexivity.
-
intros [n [v' [H [eq lv']]]].
subst v.
Lrewrite in H.
Lsimpl.
apply enc_extinj in H.
destruct mu_complete with (P:=(lam ((ext doesHaltIn) (ext s) 0))) (n:=n);try Lproc.
+
intros n0.
destruct (eva n0 s) eqn:eq;eexists; Lsimpl;reflexivity.
+
Lsimpl.
unfold doesHaltIn.
rewrite H.
reflexivity.
+
rewrite H0.
Lsimpl.
apply mu_sound in H0.
2,4:Lproc.
*
destruct H0 as [n' [eq [R _]]].
apply inj_enc in eq.
subst.
LsimplHypo.
Lrewrite in R.
apply enc_extinj in R.
unfold doesHaltIn in R.
destruct (eva n' s) eqn:eq.
2:congruence.
Lsimpl.
apply eva_equiv in H.
assert (lambda t) by now apply eva_lam in eq.
apply eva_equiv in eq.
rewrite H in eq.
unfold I.
apply unique_normal_forms in eq;[|Lproc..].
subst.
reflexivity.
*
intros n0.
eexists; Lsimpl.
Admitted.

Lemma seval_Eval n (s t:term): seval n s t -> Eval (ext s) == (ext t).
Proof.
intros.
apply seval_eva in H.
rewrite Eval_correct;try Lproc.
exists n,t.
repeat split.
-
Lsimpl.
rewrite H.
reflexivity.
-
apply eva_lam in H.
Admitted.

Lemma eval_Eval s t : eval s t -> Eval (ext s) == (ext t).
Proof.
intros H.
eapply eval_seval in H.
destruct H.
eapply seval_Eval.
Admitted.

Lemma Eval_eval (s t : term) : lambda t -> Eval (ext s) == t -> exists t', ext t' = t /\ eval s t'.
Proof with Lproc.
intros p H.
rewrite Eval_correct in H;try Lproc.
destruct H as [n [v [R [eq lv]]]].
subst t.
eexists.
split.
reflexivity.
Lrewrite in R.
apply enc_extinj in R.
apply eva_equiv in R.
split.
apply equiv_lambda;try Lproc.
assumption.
Admitted.

Lemma eval_converges s : converges s -> exists t, eval s t.
Proof.
intros [x [R ?]].
exists x.
Admitted.

Lemma Eval_converges s : converges s <-> converges (Eval (ext s)).
Proof with eauto.
split; intros H.
-
destruct (eval_converges H) as [t Ht].
pose proof (eval_Eval Ht) as He.
rewrite He.
eexists;split;[reflexivity|Lproc].
-
destruct H as [x [H l]].
apply Eval_eval in H;try Lproc.
destruct H as [t' [? t]].
exists t'.
destruct t.
split.
now rewrite H0.
Admitted.

Instance term_eva : computable eva.
Proof.
extract.

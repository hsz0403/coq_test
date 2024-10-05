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
auto.

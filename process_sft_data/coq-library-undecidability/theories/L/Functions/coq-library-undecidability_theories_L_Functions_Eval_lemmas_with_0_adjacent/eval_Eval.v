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
assumption.

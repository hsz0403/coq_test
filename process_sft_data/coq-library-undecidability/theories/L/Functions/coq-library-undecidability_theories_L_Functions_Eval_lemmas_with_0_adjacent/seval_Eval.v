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
Lproc.

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
extract.

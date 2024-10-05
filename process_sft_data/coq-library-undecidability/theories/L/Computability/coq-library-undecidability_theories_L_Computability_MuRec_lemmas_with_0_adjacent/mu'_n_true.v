From Undecidability.L Require Export Datatypes.LNat Datatypes.LBool Tactics.LTactics Computability.Computability Tactics.Lbeta.
Set Default Proof Using "Type".
Section MuRecursor.
Variable P : term.
Hypothesis P_proc : proc P.
Hint Resolve P_proc : LProc.
Hypothesis dec'_P : forall (n:nat), (exists (b:bool), app P (ext n) == ext b ).
Section hoas.
Import HOAS_Notations.
Definition mu' := Eval cbn -[enc] in rho (convert (λ mu P n, (P n) (!!K n) (λ Sn, mu P Sn) (!!(ext S) n))).
End hoas.
Import L_Notations.
Hint Resolve mu'_proc : LProc.
Definition mu :term := lam (mu' #0 (ext 0)).
Hint Resolve mu_proc : LProc.
End MuRecursor.
Hint Resolve mu'_proc : LProc.
Hint Resolve mu_proc : LProc.

Lemma mu'_n_true (n:nat): P (ext n) == ext true -> mu' P (ext n) == ext n.
Proof using P_proc.
intros R.
recStep mu'.
Lsimpl.
rewrite R.
unfold K.
now Lsimpl.

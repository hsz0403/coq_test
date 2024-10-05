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

Lemma mu_sound v : lambda v -> mu P == v -> exists n, v = ext n /\ P (ext n) == ext true /\ (forall n', n' < n -> P (ext n') == ext false).
Proof using P_proc dec'_P.
unfold mu.
intros lv R.
standardizeHypo 100.
apply mu'_sound in R.
-
destruct R as [n ?].
exists n.
intuition.
apply unique_normal_forms;try Lproc.
assumption.
-
split;[|Lproc].
apply equiv_lambda in R;auto.
apply closed_star in R;Lproc.
-
intros.
lia.

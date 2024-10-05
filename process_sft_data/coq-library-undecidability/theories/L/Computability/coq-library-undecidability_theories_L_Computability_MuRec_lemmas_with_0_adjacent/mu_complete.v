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

Lemma mu_complete (n:nat) : P (ext n) == ext true -> exists n0:nat, mu P == ext n0.
Proof using P_proc dec'_P.
remember 0 as n0.
assert (forall n':nat, n'< n-(n-n0) -> P (ext n') == ext false) by (intros;lia).
assert ((n-n0)+n0=n) by lia.
remember (n-n0) as k.
clear Heqk Heqn0 H0 n0.
induction k.
-
simpl in *.
subst.
intros.
eexists.
unfold mu.
Lsimpl.
apply mu'_complete;eauto.
intros.
apply H.
lia.
-
intros.
destruct (dec_P (n-S k)) as [y P'].
destruct y.
+
eexists.
unfold mu.
Lsimpl.
apply mu'_complete.
exact P'.
exact H.
+
apply IHk.
intros.
decide (n' = n - (S k)).
*
subst.
exact P'.
*
apply H.
lia.
*
assumption.

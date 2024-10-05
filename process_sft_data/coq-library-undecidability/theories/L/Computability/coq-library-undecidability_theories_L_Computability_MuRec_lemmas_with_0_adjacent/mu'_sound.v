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

Lemma mu'_sound v n: proc v -> mu' P (ext (n:nat)) == v -> (forall n', n' < n -> P (ext n') == ext false) -> exists n0, n0 >= n /\ P (ext n0) == ext true /\ v == ext n0 /\ forall n', n' < n0 -> P (ext (n':nat)) == ext false.
Proof using P_proc dec'_P.
intros pv.
intros R.
apply equiv_lambda in R;try Lproc.
apply star_pow in R.
destruct R as [k R].
revert n R.
apply complete_induction with (x:=k);clear k;intros k.
intros IH n R H.
specialize (dec_P n).
destruct (dec_P n) as [[] eq].
-
exists n;intuition.
apply pow_star in R.
apply star_equiv in R.
rewrite <- R.
now rewrite mu'_n_true.
-
assert (R':=mu'_n_false eq).
apply star_pow in R'.
destruct R' as [k' R'].
destruct (parametrized_confluence uniform_confluence R R') as [x [l [u [le1 [le2 [R1 [R2 eq']]]]]]].
destruct x.
+
inv R1.
apply IH in R2 as [n0 [ge1 [Rn0 [eq0 H0]]]].
*
exists n0.
repeat split;try assumption;lia.
*
decide (l=k);[|lia].
subst l.
assert (k'=0) by lia.
subst k'.
inv R'.
apply inj_enc in H1.
lia.
*
intros.
decide (n'=n).
subst.
tauto.
apply H.
lia.
+
destruct R1 as [? [C _]].
destruct pv as [_ [v']].
subst v.
inv C.

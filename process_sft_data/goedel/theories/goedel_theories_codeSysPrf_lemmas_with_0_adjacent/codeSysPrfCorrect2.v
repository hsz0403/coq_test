Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import checkPrf.
Require Import code.
Require Import Languages.
Require Import folProp.
Require Import folProof.
Require Import folLogic3.
Require Import folReplace.
Require Import PRrepresentable.
Require Import expressible.
Require Import primRec.
Require Import Arith.
Require Import PA.
Require Import NNtheory.
Require Import codeList.
Require Import subProp.
Require Import ListExt.
Require Import cPair.
Require Import wellFormed.
Require Import prLogic.
Ltac SimplFreeVar := repeat match goal with | H1:(?X1 = ?X2),H2:(?X1 <> ?X2) |- _ => elim H2; apply H1 | H1:(?X1 = ?X2),H2:(?X2 <> ?X1) |- _ => elim H2; symmetry in |- *; apply H1 | H1:(?X1 <> ?X1) |- _ => elim H1; reflexivity | H:(In ?X3 (freeVarFormula ?X9 (existH ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula X9 X2))); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.existH ?X9 ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula X9 X2))); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (forallH ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula X9 X2))); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.forallH ?X9 ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula X9 X2))); [ apply H | clear H ] | H:(In ?X3 (list_remove nat eq_nat_dec ?X1 (freeVarFormula ?X9 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X2)); [ eapply In_list_remove1; apply H | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ] | H:(In ?X3 (freeVarFormula ?X9 (andH ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.andH ?X9 ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (orH ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.orH ?X9 ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (impH ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.impH ?X9 ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (notH ?X1))) |- _ => assert (In X3 (freeVarFormula X9 X1)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.notH ?X9 ?X1))) |- _ => assert (In X3 (freeVarFormula X9 X1)); [ apply H | clear H ] | H:(In _ (_ ++ _)) |- _ => induction (in_app_or _ _ _ H); clear H | H:(In _ (freeVarFormula ?X9 (substituteFormula ?X9 ?X1 ?X2 ?X3))) |- _ => induction (freeVarSubFormula3 _ _ _ _ _ H); clear H | H:(In _ (freeVarFormula ?X9 (LT ?X1 ?X2))) |- _ => rewrite freeVarLT in H | H:(In _ (freeVarTerm ?X9 (LNT.natToTerm _))) |- _ => elim (LNT.closedNatToTerm _ _ H) | H:(In _ (freeVarTerm ?X9 (natToTerm _))) |- _ => elim (closedNatToTerm _ _ H) | H:(In _ (freeVarTerm ?X9 Zero)) |- _ => elim H | H:(In _ (freeVarTerm ?X9 (Succ _))) |- _ => rewrite freeVarSucc in H | H:(In _ (freeVarTerm ?X9 (var _))) |- _ => simpl in H; decompose sum H; clear H | H:(In _ (freeVarTerm ?X9 (LNT.var _))) |- _ => simpl in H; decompose sum H; clear H | H:(In _ (freeVarTerm ?X9 (fol.var ?X9 _))) |- _ => simpl in H; decompose sum H; clear H end.
Section code_SysPrf.
Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.
Variable codeArityF : nat -> nat.
Variable codeArityR : nat -> nat.
Hypothesis codeArityFIsPR : isPR 1 codeArityF.
Hypothesis codeArityFIsCorrect1 : forall f : Functions L, codeArityF (codeF f) = S (arity L (inr _ f)).
Hypothesis codeArityFIsCorrect2 : forall n : nat, codeArityF n <> 0 -> exists f : Functions L, codeF f = n.
Hypothesis codeArityRIsPR : isPR 1 codeArityR.
Hypothesis codeArityRIsCorrect1 : forall r : Relations L, codeArityR (codeR r) = S (arity L (inl _ r)).
Hypothesis codeArityRIsCorrect2 : forall n : nat, codeArityR n <> 0 -> exists r : Relations L, codeR r = n.
Hypothesis codeFInj : forall f g : Functions L, codeF f = codeF g -> f = g.
Hypothesis codeRInj : forall R S : Relations L, codeR R = codeR S -> R = S.
Section LNN.
Variable T : System.
Hypothesis TextendsNN : Included _ NN T.
Variable U : fol.System L.
Variable fU : Formula.
Variable v0 : nat.
Hypothesis freeVarfU : forall v : nat, In v (freeVarFormula LNN fU) -> v = v0.
Hypothesis expressU1 : forall f : fol.Formula L, mem _ U f -> SysPrf T (substituteFormula LNN fU v0 (natToTerm (codeFormula L codeF codeR f))).
Hypothesis expressU2 : forall f : fol.Formula L, ~ mem _ U f -> SysPrf T (notH (substituteFormula LNN fU v0 (natToTerm (codeFormula L codeF codeR f)))).
Definition codeSysPrf : Formula := let nv := newVar (2 :: 1 :: 0 :: v0 :: nil) in existH nv (andH (substituteFormula LNN (substituteFormula LNN (primRecFormula 2 (proj1_sig (checkPrfIsPR L codeF codeR codeArityF codeArityR codeArityFIsPR codeArityRIsPR))) 0 (Succ (var nv))) 2 (var 0)) (forallH (S nv) (impH (LT (var (S nv)) (var nv)) (orH (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (primRecFormula 2 (proj1_sig codeInIsPR)) 2 (var (S nv))) 1 (var nv)) 0 Zero) (substituteFormula LNN fU v0 (var (S nv))))))).
Definition codeSysPf : Formula := existH 1 codeSysPrf.
Definition codeSysPrfNot := existH 2 (andH (substituteFormula LNN codeSysPrf 0 (var 2)) (substituteFormula LNN (substituteFormula LNN (primRecFormula 1 (proj1_sig codeNotIsPR)) 0 (var 2)) 1 (var 0))).
End LNN.
End code_SysPrf.

Lemma codeSysPrfCorrect2 : forall (f : fol.Formula L) (A : fol.Formulas L), (exists g : fol.Formula L, In g A /\ ~ mem _ U g) -> forall p : Prf L A f, SysPrf T (notH (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm (codePrf L codeF codeR A f p)))).
Proof.
intros.
unfold codeSysPrf in |- *.
set (nvl := 2 :: 1 :: 0 :: v0 :: nil) in *.
set (nv := newVar nvl) in *.
assert (nv <> 0).
unfold nv, not in |- *; intros; elim (newVar1 nvl).
rewrite H0; unfold nvl in |- *.
simpl in |- *; auto.
assert (nv <> 1).
unfold nv, not in |- *; intros; elim (newVar1 nvl).
rewrite H1; unfold nvl in |- *.
simpl in |- *; auto.
assert (nv <> 2).
unfold nv, not in |- *; intros; elim (newVar1 nvl).
rewrite H2; unfold nvl in |- *.
simpl in |- *; auto.
assert (nv <> v0).
unfold nv, not in |- *; intros; elim (newVar1 nvl).
rewrite H3; unfold nvl in |- *.
simpl in |- *; auto.
set (F := primRecFormula 2 (proj1_sig (checkPrfIsPR L codeF codeR codeArityF codeArityR codeArityFIsPR codeArityRIsPR))) in *.
set (J := primRecFormula 2 (proj1_sig codeInIsPR)) in *.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec nv 0).
elim H0; assumption.
induction (In_dec eq_nat_dec nv (freeVarTerm LNN (natToTerm (codeFormula L codeF codeR f)))).
elim (closedNatToTerm _ _ a).
clear b b0.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec nv 1).
elim H1; assumption.
induction (In_dec eq_nat_dec nv (freeVarTerm LNN (natToTerm (codePrf L codeF codeR A f p)))).
elim (closedNatToTerm _ _ a).
clear b b0.
repeat rewrite (subFormulaAnd LNN).
apply nExist.
set (n := codePrf L codeF codeR A f p) in *.
apply impE with (forallH nv (notH (fol.andH LNN (equal (Succ (var nv)) (natToTerm (checkPrf L codeF codeR codeArityF codeArityR (codeFormula L codeF codeR f) n))) (substituteFormula LNN (substituteFormula LNN (forallH (S nv) (impH (LT (var (S nv)) (var nv)) (orH (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)) 0 Zero) (substituteFormula LNN fU v0 (var (S nv)))))) 0 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm n))))).
apply sysExtend with NN.
assumption.
apply iffE2.
apply (reduceForall LNN).
apply closedNN.
apply (reduceNot LNN).
apply (reduceAnd LNN).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN F 2 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm n)) 0 (Succ (var nv))).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN F 0 (Succ (var nv))) 2 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm n)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In 0 (freeVarFormula LNN (substituteFormula LNN F 0 (Succ (var nv))))).
eapply In_list_remove1.
apply H4.
induction (freeVarSubFormula3 _ _ _ _ _ H5).
elim (In_list_remove2 _ _ _ _ _ H6).
reflexivity.
simpl in H6.
decompose sum H6.
apply H0; assumption.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN F 2 (natToTerm (codeFormula L codeF codeR f))) 0 (Succ (var nv))) 1 (natToTerm n)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
simpl in H4.
decompose sum H4.
apply H2; assumption.
apply closedNatToTerm.
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
simpl in H4.
decompose sum H4.
apply H1; assumption.
apply closedNatToTerm.
assert (Representable NN 2 (checkPrf L codeF codeR codeArityF codeArityR) (primRecFormula 2 (proj1_sig (checkPrfIsPR L codeF codeR codeArityF codeArityR codeArityFIsPR codeArityRIsPR)))).
apply primRecRepresentable.
fold F in H4.
induction H4 as (H4, H5).
simpl in H5.
apply iffTrans with (substituteFormula LNN (equal (var 0) (natToTerm (checkPrf L codeF codeR codeArityF codeArityR (codeFormula L codeF codeR f) n))) 0 (Succ (var nv))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply H5.
rewrite (subFormulaEqual LNN).
rewrite (subTermVar1 LNN).
rewrite (subTermNil LNN).
apply iffRefl.
apply closedNatToTerm.
apply iffRefl.
unfold n in |- *.
rewrite checkPrfCorrect1.
decompose record H.
apply impE with (notH (substituteFormula LNN fU v0 (natToTerm (codeFormula L codeF codeR x)))).
apply sysExtend with NN.
assumption.
apply impI.
assert (forall v : nat, ~ In v (freeVarFormula LNN (notH (substituteFormula LNN fU v0 (natToTerm (codeFormula L codeF codeR x)))))).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H4).
absurd (v = v0).
eapply In_list_remove2.
apply H7.
apply freeVarfU.
eapply In_list_remove1.
apply H7.
apply (closedNatToTerm _ _ H7).
assert (forall v : nat, ~ In_freeVarSys LNN v (Ensembles.Add (fol.Formula LNN) NN (notH (substituteFormula LNN fU v0 (natToTerm (codeFormula L codeF codeR x)))))).
unfold not in |- *; intros.
induction H7 as (x0, H7); induction H7 as (H7, H8).
induction H8 as [x0 H8| x0 H8].
elim (closedNN v).
exists x0.
auto.
induction H8.
apply (H4 v).
assumption.
apply forallI.
apply H7.
apply nAnd.
unfold orH at 1 in |- *.
unfold fol.orH in |- *.
apply impTrans with (equal (Succ (var nv)) (natToTerm (S (codeList (map (codeFormula L codeF codeR) A))))).
apply impI.
apply nnE.
apply Axm; right; constructor.
apply impI.
rewrite <- (subFormulaId LNN (notH (substituteFormula LNN (substituteFormula LNN (forallH (S nv) (impH (LT (var (S nv)) (var nv)) (orH (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)) 0 Zero) (substituteFormula LNN fU v0 (var (S nv)))))) 0 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm (codePrf L codeF codeR A f p)))) nv) .
apply impE with (substituteFormula LNN (notH (substituteFormula LNN (substituteFormula LNN (forallH (S nv) (impH (LT (var (S nv)) (var nv)) (orH (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)) 0 Zero) (substituteFormula LNN fU v0 (var (S nv)))))) 0 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm (codePrf L codeF codeR A f p)))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))).
apply (subWithEquals LNN).
apply eqSym.
apply impE with (fol.equal LNN (Succ (var nv)) (natToTerm (S (codeList (map (codeFormula L codeF codeR) A))))).
apply sysWeaken.
fold var in |- *.
simpl in |- *.
apply sysWeaken.
apply nn2.
apply Axm; right; constructor.
apply sysWeaken.
assert (S nv <> 1).
unfold not in |- *; intros.
elim (le_not_lt (S nv) 1).
rewrite H8.
apply le_n.
apply lt_S.
unfold nv in |- *.
apply newVar2.
unfold nvl in |- *; simpl in |- *; auto.
assert (S nv <> 2).
unfold not in |- *; intros.
elim (le_not_lt (S nv) 2).
rewrite H9.
apply le_n.
apply lt_S.
unfold nv in |- *.
apply newVar2.
unfold nvl in |- *; simpl in |- *; auto.
assert (S nv <> nv).
unfold not in |- *; intros.
eapply (n_Sn nv).
symmetry in |- *; assumption.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec (S nv) 0).
discriminate a.
induction (In_dec eq_nat_dec (S nv) (freeVarTerm LNN (natToTerm (codeFormula L codeF codeR f)))).
elim (closedNatToTerm _ _ a).
clear b b0.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec (S nv) 1).
elim H8; assumption.
induction (In_dec eq_nat_dec (S nv) (freeVarTerm LNN (natToTerm (codePrf L codeF codeR A f p)))).
elim (closedNatToTerm _ _ a).
clear b b0.
rewrite (subFormulaNot LNN).
rewrite (subFormulaForall LNN).
induction (eq_nat_dec (S nv) nv).
elim H10; assumption.
induction (In_dec eq_nat_dec (S nv) (freeVarTerm LNN (natToTerm (codeList (map (codeFormula L codeF codeR) A))))).
elim (closedNatToTerm _ _ a).
clear b b0.
apply nForall.
apply existI with (natToTerm (codeFormula L codeF codeR x)).
rewrite (subFormulaNot LNN).
repeat rewrite (subFormulaImp LNN).
apply nImp.
apply andI.
assert (forall (t1 t2 s : Term) (v : nat), substituteFormula LNN (LT t1 t2) v s = LT (substituteTerm LNN t1 v s) (substituteTerm LNN t2 v s)).
reflexivity.
repeat rewrite H11.
repeat rewrite (subTermVar1 LNN) || rewrite (subTermVar2 LNN); try unfold not in |- *; intros.
rewrite (subTermNil LNN).
apply sysWeaken.
apply natLT.
cut (In x A).
generalize x A.
intros.
induction A0 as [| a A0 HrecA0].
elim H12.
induction H12 as [H12| H12].
rewrite H12.
simpl in |- *.
apply le_lt_n_Sm.
apply cPairLe1.
apply lt_le_trans with (codeList (map (codeFormula L codeF codeR) A0)).
auto.
simpl in |- *.
apply le_S.
apply cPairLe2.
assumption.
apply closedNatToTerm.
apply H1; auto.
apply H0; auto.
apply H10; auto.
apply H8; auto.
discriminate H12.
repeat rewrite (subFormulaOr LNN).
apply nOr.
apply andI.
apply sysWeaken.
assert (Representable NN 2 codeIn J).
unfold J in |- *; apply primRecRepresentable.
induction H11 as (H11, H12).
apply impE with (notH (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (natToTerm (codeFormula L codeF codeR x))) 1 (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) 0 Zero)).
apply cp2.
apply iffE1.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)) 0 Zero) 1 (natToTerm (codePrf L codeF codeR A f p))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm (codeFormula L codeF codeR x))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H13).
elim (In_list_remove2 _ _ _ _ _ H14).
reflexivity.
apply H14.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)) 1 (natToTerm (codePrf L codeF codeR A f p))) 0 Zero) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm (codeFormula L codeF codeR x))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
auto.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)) 0 Zero) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm (codeFormula L codeF codeR x))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H13).
elim (In_list_remove2 _ _ _ _ _ H14).
reflexivity.
simpl in H14.
decompose sum H14.
apply H1; assumption.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) 0 Zero) (S nv) (natToTerm (codeFormula L codeF codeR x))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
unfold not in |- *; intros.
apply H0; symmetry in |- *; assumption.
auto.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) 0 Zero) (S nv) (natToTerm (codeFormula L codeF codeR x))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In nv (freeVarFormula LNN (substituteFormula LNN J 2 (var (S nv))))).
eapply In_list_remove1.
apply H13.
induction (freeVarSubFormula3 _ _ _ _ _ H14).
apply (le_not_lt nv 2).
apply H11.
eapply In_list_remove1.
apply H15.
destruct nv as [| n0].
elim H0; reflexivity.
destruct n0.
elim H1; reflexivity.
destruct n0.
elim H2; reflexivity.
repeat apply lt_n_S.
apply lt_O_Sn.
simpl in H15.
decompose sum H15.
apply H10; assumption.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm (codeFormula L codeF codeR x))) 0 Zero).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
auto.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) (S nv) (natToTerm (codeFormula L codeF codeR x))) 1 (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) 0 Zero).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
unfold not in |- *; intros.
apply H8; symmetry in |- *; assumption.
apply closedNatToTerm.
apply closedNatToTerm.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
apply (le_not_lt (S nv) 2).
apply H11.
eapply In_list_remove1.
apply H13.
destruct nv as [| n0].
elim H8; reflexivity.
destruct n0.
elim H9; reflexivity.
repeat apply lt_n_S.
apply lt_O_Sn.
simpl in H12.
apply impE with (notH (substituteFormula LNN (equal (var 0) (natToTerm (codeIn (codeFormula L codeF codeR x) (codeList (map (codeFormula L codeF codeR) A))))) 0 Zero)).
apply cp2.
apply iffE1.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply H12.
rewrite (subFormulaEqual LNN).
rewrite (subTermVar1 LNN).
rewrite (subTermNil LNN).
rewrite codeInCorrect.
induction (In_dec eq_nat_dec (codeFormula L codeF codeR x) (map (codeFormula L codeF codeR) A)).
replace Zero with (natToTerm 0).
apply natNE.
discriminate.
reflexivity.
elim b.
cut (In x A).
generalize A x.
intros.
induction A0 as [| a A0 HrecA0].
elim H13.
induction H13 as [H13| H13].
rewrite H13.
simpl in |- *.
auto.
simpl in |- *.
auto.
assumption.
apply closedNatToTerm.
apply impE with (notH (substituteFormula LNN fU v0 (natToTerm (codeFormula L codeF codeR x)))).
apply sysWeaken.
apply cp2.
apply iffE1.
assert (forall v : nat, ~ In v (list_remove nat eq_nat_dec v0 (freeVarFormula LNN fU))).
unfold not in |- *; intros.
absurd (v = v0).
eapply In_list_remove2.
apply H11.
apply freeVarfU.
eapply In_list_remove1.
apply H11.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN fU v0 (var (S nv))) 1 (natToTerm (codePrf L codeF codeR A f p))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm (codeFormula L codeF codeR x))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H12).
apply (H11 0).
assumption.
simpl in H13.
decompose sum H13.
discriminate H14.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN fU v0 (var (S nv))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm (codeFormula L codeF codeR x))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H12).
apply (H11 1).
assumption.
simpl in H13.
decompose sum H13.
apply H8; assumption.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN fU v0 (var (S nv))) (S nv) (natToTerm (codeFormula L codeF codeR x))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H12).
apply (H11 nv).
assumption.
simpl in H13.
decompose sum H13.
apply H10; assumption.
apply (subFormulaTrans LNN).
apply H11.
apply Axm; right; constructor.
apply expressU2.
assumption.
assumption.
assumption.

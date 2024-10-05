Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import folProp.
Require Import folProof.
Require Import folReplace.
Require Import folLogic3.
Require Import subProp.
Require Import ListExt.
Require Import NNtheory.
Require Import NN2PA.
Require Import fixPoint.
Require Import codeSysPrf.
Require Import PAtheory.
Require Import code.
Require Import PRrepresentable.
Require Import expressible.
Require Import checkPrf.
Require Import codeNatToTerm.
Section Rosser's_Incompleteness.
Definition codeFormula := codeFormula LNT codeLNTFunction codeLNTRelation.
Variable T : System.
Definition T' : fol.System LNN := Union _ NN (fun x : fol.Formula LNN => mem _ T (LNN2LNT_formula x)).
Hypothesis extendsPA : Included _ PA T.
Variable repT : Formula.
Variable v0 : nat.
Hypothesis freeVarRepT : forall v : nat, In v (freeVarFormula LNT repT) -> v = v0.
Hypothesis expressT1 : forall f : Formula, mem _ T f -> SysPrf T (substituteFormula LNT repT v0 (natToTerm (codeFormula f))).
Hypothesis expressT2 : forall f : Formula, ~ mem _ T f -> SysPrf T (notH (substituteFormula LNT repT v0 (natToTerm (codeFormula f)))).
Definition codeSysPrf := codeSysPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR (LNT2LNN_formula repT) v0.
Definition codeSysPrfCorrect1 := codeSysPrfCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0 freeVarRepT' expressT'1.
Definition codeSysPrfCorrect2 := codeSysPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0 freeVarRepT' expressT'2.
Definition codeSysPrfCorrect3 := codeSysPrfCorrect3 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2 codeArityLNTRIsPR codeArityLNTRIsCorrect1 codeArityLNTRIsCorrect2 codeLNTFunctionInj codeLNTRelationInj T' extendsNN.
Definition codePrf := codePrf LNT codeLNTFunction codeLNTRelation.
Definition codeSysPrfNot := codeSysPrfNot LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR (LNT2LNN_formula repT) v0.
Definition freeVarCodeSysPrfN := freeVarCodeSysPrfN LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR (LNT2LNN_formula repT) v0 freeVarRepT'.
Definition codeSysPrfNCorrect1 := codeSysPrfNCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0 freeVarRepT' expressT'1.
Definition codeSysPrfNCorrect2 := codeSysPrfNCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0 freeVarRepT' expressT'2.
Definition codeSysPrfNCorrect3 := codeSysPrfNCorrect3 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2 codeArityLNTRIsPR codeArityLNTRIsCorrect1 codeArityLNTRIsCorrect2 codeLNTFunctionInj codeLNTRelationInj T' extendsNN (LNT2LNN_formula repT) v0 freeVarRepT'.
End Rosser's_Incompleteness.
Require Import codePA.
Require Import PAconsistent.

Theorem Rosser'sIncompleteness : (forall x : Formula, mem _ T x \/ ~ mem _ T x) -> exists f : Formula, (forall v : nat, ~ In v (freeVarFormula LNT f)) /\ (SysPrf T f \/ SysPrf T (notH f) -> Inconsistent LNT T).
Proof.
intros decide.
set (A := fol.forallH LNN 1 (fol.impH LNN codeSysPrf (fol.existH LNN 2 (fol.andH LNN (LNN.LT (fol.var LNN 2) (fol.var LNN 1)) (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))))) in *.
destruct (FixPointLNT (LNN2LNT_formula A) 0) as [x [H0 H1]].
exists x.
split.
unfold not in |- *; intros.
induction (H1 v).
assert (In v (list_remove nat eq_nat_dec 0 (freeVarFormula LNT (LNN2LNT_formula A)))).
apply H2.
assumption.
cut (In v (list_remove nat eq_nat_dec 0 (freeVarFormula LNN A))).
clear H4.
intros.
unfold A in H4.
SimplFreeVar.
assert (v <= 1).
apply (freeVarCodeSysPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR (LNT2LNN_formula repT) v0 freeVarRepT').
apply H5.
destruct v as [| n].
apply H6.
reflexivity.
destruct n.
apply H7.
reflexivity.
apply (le_not_lt (S (S n)) 1).
assumption.
apply lt_n_S.
apply lt_O_Sn.
assert (v <= 1).
apply freeVarCodeSysPrfN.
assumption.
destruct v as [| n].
apply H6.
reflexivity.
destruct n.
apply H7.
reflexivity.
apply (le_not_lt (S (S n)) 1).
assumption.
apply lt_n_S.
apply lt_O_Sn.
eapply In_list_remove3.
apply LNN2LNT_freeVarFormula1.
eapply In_list_remove1.
apply H4.
eapply In_list_remove2.
apply H4.
intros.
induction H as [H| H].
unfold Inconsistent in |- *.
intros.
elim H.
intros.
induction H2 as (x1, H2).
induction (searchProof decide _ (notH x) _ x1).
decompose record H3.
apply contradiction with x.
assumption.
exists x2.
exists x3.
assumption.
apply contradiction with (existH 2 (andH (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (natToTermLNN (codePrf _ _ x1)))) (substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0 (natToTerm (codeFormula x))) 1 (var 2)))).
apply impE with (existH 2 (andH (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (natToTermLNN (codePrf x0 x x1)))) (substituteFormula LNT (substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0 (natToTerm (codeFormula x))) 1 (var 2)) 1 (natToTerm (codePrf _ _ x1))))).
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
apply (reduceExist LNT).
apply closedPA.
apply (reduceAnd LNT).
apply iffRefl.
apply (subFormulaNil LNT).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H4).
apply (In_list_remove2 _ _ _ _ _ H5).
reflexivity.
simpl in H5.
decompose sum H5.
discriminate H6.
replace (LNN.LT (fol.var LNN 2) (natToTermLNN (codePrf _ _ x1))) with (substituteFormula LNN (LNN.LT (fol.var LNN 2) (fol.var LNN 1)) 1 (natToTermLNN (codePrf _ _ x1))).
apply impE with (existH 2 (andH (substituteFormula LNT (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) 1 (natToTerm (codePrf x0 x x1))) (substituteFormula LNT (substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0 (natToTerm (codeFormula x))) 1 (var 2)) 1 (natToTerm (codePrf x0 x x1))))).
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
apply (reduceExist LNT).
apply closedPA.
apply (reduceAnd LNT).
apply iffSym.
rewrite <- LNN2LNT_natToTerm.
apply LNN2LNT_subFormula.
apply iffRefl.
rewrite <- (subFormulaAnd LNT).
apply impE with (existH 2 (substituteFormula LNT (fol.andH LNT (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) (substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 1 (var 2)) 0 (natToTerm (codeFormula x)))) 1 (natToTerm (codePrf x0 x x1)))).
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
apply (reduceExist LNT).
apply closedPA.
apply (reduceSub LNT).
apply closedPA.
apply (reduceAnd LNT).
apply iffRefl.
apply (subFormulaExch LNT).
discriminate.
unfold not in |- *; intros.
simpl in H4.
decompose sum H4.
discriminate H5.
apply closedNatToTerm.
replace (LNN.LT (fol.var LNN 2) (fol.var LNN 1)) with (substituteFormula LNN (LNN.LT (fol.var LNN 2) (fol.var LNN 1)) 0 (natToTermLNN (codeFormula x))).
apply impE with (existH 2 (substituteFormula LNT (fol.andH LNT (substituteFormula LNT (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) 0 (natToTerm (codeFormula x))) (substituteFormula LNT (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))) 0 (natToTerm (codeFormula x)))) 1 (natToTerm (codePrf x0 x x1)))).
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
apply (reduceExist LNT).
apply closedPA.
apply (reduceSub LNT).
apply closedPA.
apply (reduceAnd LNT).
apply iffSym.
rewrite <- LNN2LNT_natToTerm.
apply LNN2LNT_subFormula.
apply (reduceSub LNT).
apply closedPA.
replace (var 2) with (LNN2LNT_term (fol.var LNN 2)).
apply LNN2LNT_subFormula.
reflexivity.
rewrite <- (subFormulaAnd LNT).
replace (existH 2 (substituteFormula LNT (substituteFormula LNT (fol.andH LNT (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))) 0 (natToTerm (codeFormula x))) 1 (natToTerm (codePrf x0 x x1)))) with (substituteFormula LNT (existH 2 (substituteFormula LNT (fol.andH LNT (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))) 0 (natToTerm (codeFormula x)))) 1 (natToTerm (codePrf x0 x x1))).
replace (existH 2 (substituteFormula LNT (fol.andH LNT (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))) 0 (natToTerm (codeFormula x)))) with (substituteFormula LNT (existH 2 (fol.andH LNT (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))))) 0 (natToTerm (codeFormula x))).
apply impE with (substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrf) 0 (natToTerm (codeFormula x))) 1 (natToTerm (codePrf _ _ x1))).
repeat rewrite <- (subFormulaImp LNT).
apply forallE.
replace (forallH 1 (substituteFormula LNT (fol.impH LNT (LNN2LNT_formula codeSysPrf) (existH 2 (fol.andH LNT (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2)))))) 0 (natToTerm (codeFormula x)))) with (substituteFormula LNT (forallH 1 (fol.impH LNT (LNN2LNT_formula codeSysPrf) (existH 2 (fol.andH LNT (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))))))) 0 (natToTerm (codeFormula x))).
apply impE with x.
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
apply H0.
assumption.
rewrite (subFormulaForall LNT).
induction (eq_nat_dec 1 0).
discriminate a.
induction (In_dec eq_nat_dec 1 (freeVarTerm LNT (natToTerm (codeFormula x)))).
elim (closedNatToTerm _ _ a).
reflexivity.
apply impE with (LNN2LNT_formula (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN (codePrf x0 x x1)))).
apply iffE1.
apply sysExtend with PA.
apply extendsPA.
eapply iffTrans.
apply LNN2LNT_subFormula.
repeat rewrite <- LNN2LNT_natToTerm.
apply (reduceSub LNT).
apply closedPA.
apply LNN2LNT_subFormula.
apply T'prf2Tprf.
apply codeSysPrfCorrect1.
assumption.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 2 0).
discriminate a.
induction (In_dec eq_nat_dec 2 (freeVarTerm LNT (natToTerm (codeFormula x)))).
elim (closedNatToTerm _ _ a).
reflexivity.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 2 1).
discriminate a.
induction (In_dec eq_nat_dec 2 (freeVarTerm LNT (natToTerm (codePrf x0 x x1)))).
elim (closedNatToTerm _ _ a).
reflexivity.
unfold LNN.LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
reflexivity.
unfold LNN.LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
reflexivity.
apply nExist.
set (E := LNN2LNT_formula (nat_rec (fun _ => fol.Formula LNN) (LNT2LNN_formula (equal Zero Zero)) (fun (n : nat) rec => fol.andH LNN (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrfNot 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n))) rec) (codePrf x0 x x1))) in *.
assert (forall x : nat, ~ In x (freeVarFormula LNT E)).
unfold E in |- *.
clear H3 E.
induction (codePrf x0 x x1).
simpl in |- *.
auto.
intros.
unfold nat_rec, nat_rect in |- *.
unfold not in |- *; intros.
set (Q := (fix F (n : nat) : (fun _ : nat => fol.Formula LNN) n := match n with | O => LNT2LNN_formula (equal Zero Zero) | S n0 => (fun (n1 : nat) (rec : fol.Formula LNN) => fol.andH LNN (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrfNot 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n1))) rec) n0 (F n0) end) n) in *.
assert (In x2 (freeVarFormula LNN (fol.andH LNN (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrfNot 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n))) Q))).
apply LNN2LNT_freeVarFormula1.
assumption.
clear H3.
SimplFreeVar.
apply (le_not_lt x2 1).
apply freeVarCodeSysPrfN.
assumption.
destruct x2 as [| n0].
elim H6; reflexivity.
destruct n0.
elim H5; reflexivity.
apply lt_n_S.
apply lt_O_Sn.
rewrite <- LNT2LNN_natToTerm in H4.
rewrite LNT2LNN_freeVarTerm in H4.
apply (closedNatToTerm _ _ H4).
rewrite <- LNT2LNN_natToTerm in H4.
rewrite LNT2LNN_freeVarTerm in H4.
apply (closedNatToTerm _ _ H4).
apply (IHn x2).
apply LNN2LNT_freeVarFormula2.
assumption.
apply impE with E.
apply sysExtend with PA.
apply extendsPA.
apply impI.
apply forallI.
unfold not in |- *; intros.
induction H5 as (x2, H5).
induction H5 as (H5, H6).
induction H6 as [x2 H6| x2 H6].
apply (closedPA 2).
exists x2.
auto.
induction H6.
apply (H4 2).
assumption.
apply nAnd.
unfold orH, fol.orH in |- *.
apply impTrans with (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (natToTermLNN (codePrf x0 x x1)))).
apply impI.
apply nnE.
apply Axm; right; constructor.
apply impI.
apply impE with E.
apply impE with (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (natToTermLNN (codePrf x0 x x1)))).
do 2 apply sysWeaken.
apply PAboundedLT.
intros.
rewrite (subFormulaImp LNT).
rewrite (subFormulaNot LNT).
apply impE with (fol.impH LNT E (fol.notH LNT (substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0 (natToTerm (codeFormula x))) 1 (natToTerm n)))).
apply iffE2.
apply (reduceImp LNT).
apply (subFormulaNil LNT).
apply H4.
apply (reduceNot LNT).
apply (subFormulaTrans LNT).
unfold not in |- *; intros.
SimplFreeVar.
apply (le_not_lt 2 1).
apply freeVarCodeSysPrfN.
apply LNN2LNT_freeVarFormula1.
apply H7.
apply lt_n_Sn.
unfold E in |- *.
clear E H4 H3.
apply impI.
induction (codePrf x0 x x1).
elim (lt_n_O _ H5).
unfold nat_rec, nat_rect in |- *.
set (Q := (fix F (n1 : nat) : (fun _ : nat => fol.Formula LNN) n1 := match n1 with | O => LNT2LNN_formula (equal Zero Zero) | S n2 => (fun (n3 : nat) (rec : fol.Formula LNN) => fol.andH LNN (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrfNot 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n3))) rec) n2 (F n2) end) n0) in *.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)).
apply impE with (LNN2LNT_formula Q).
apply sysWeaken.
apply impI.
apply (IHn0 H3).
rewrite LNN2LNT_and.
eapply andE2.
apply Axm; right; constructor.
rewrite H3.
apply impE with (LNN2LNT_formula (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrfNot 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n0)))).
apply sysWeaken.
apply iffE1.
apply iffTrans with (notH (LNN2LNT_formula (substituteFormula LNN (substituteFormula LNN codeSysPrfNot 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n0)))).
apply iffRefl.
apply (reduceNot LNT).
rewrite <- LNN2LNT_natToTerm.
rewrite <- LNN2LNT_natToTerm.
apply iffTrans with (substituteFormula LNT (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 0 (natToTermLNN (codeFormula x)))) 1 (LNN2LNT_term (natToTermLNN n0))).
apply LNN2LNT_subFormula.
apply (reduceSub LNT).
apply closedPA.
apply LNN2LNT_subFormula.
eapply andE1.
rewrite LNN2LNT_and.
apply Axm; right; constructor.
apply Axm; right; constructor.
apply Axm; left; right; constructor.
unfold E in |- *.
clear H4 E.
induction (codePrf x0 x x1).
simpl in |- *.
apply eqRefl.
unfold nat_rec, nat_rect in |- *.
rewrite LNN2LNT_and.
apply andI.
induction (eq_nat_dec (checkPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR (codeFormula (notH x)) n) 0).
unfold codeSysPrfNot in |- *.
apply T'prf2Tprf.
apply codeSysPrfNCorrect3.
unfold not in |- *; intros.
rewrite H4 in a.
rewrite (checkPrfCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTRIsCorrect1) in a.
discriminate a.
decompose record (checkPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2 codeArityLNTRIsCorrect1 codeArityLNTRIsCorrect2 codeLNTFunctionInj codeLNTRelationInj _ _ b).
rewrite <- H6.
assert (x2 = notH x).
eapply codeFormulaInj.
apply codeLNTFunctionInj.
apply codeLNTRelationInj.
assumption.
cut (code.codePrf LNT codeLNTFunction codeLNTRelation x3 x2 x4 = n).
generalize x4.
clear H6 x4.
rewrite H4.
intros.
apply T'prf2Tprf.
apply codeSysPrfNCorrect2.
eapply H3.
apply lt_S.
rewrite <- H6.
apply lt_n_Sn.
assumption.
apply IHn.
intros.
eapply H3.
apply lt_S.
apply H4.
unfold Inconsistent in |- *.
intros.
elim H.
intros.
induction H2 as (x1, H2).
induction (searchProof decide _ x _ x1).
decompose record H3.
apply contradiction with x.
exists x2.
exists x3.
assumption.
assumption.
apply contradiction with (substituteFormula LNT (LNN2LNT_formula A) 0 (natToTermLNT (code.codeFormula LNT codeLNTFunction codeLNTRelation x))).
unfold A in |- *.
replace (LNN2LNT_formula (fol.forallH LNN 1 (fol.impH LNN codeSysPrf (fol.existH LNN 2 (fol.andH LNN (LNN.LT (fol.var LNN 2) (fol.var LNN 1)) (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))))))) with (forallH 1 (impH (LNN2LNT_formula codeSysPrf) (existH 2 (andH (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))))))).
rewrite (subFormulaForall LNT).
induction (eq_nat_dec 1 0).
discriminate a.
induction (In_dec eq_nat_dec 1 (freeVarTerm LNT (natToTermLNT (code.codeFormula LNT codeLNTFunction codeLNTRelation x)))).
elim (closedNatToTerm _ _ a).
clear b0 b.
set (E := LNN2LNT_formula (nat_rec (fun _ => fol.Formula LNN) (LNT2LNN_formula (equal Zero Zero)) (fun (n : nat) rec => fol.andH LNN (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n))) rec) (S (codePrf _ _ x1)))) in *.
assert (forall x : nat, ~ In x (freeVarFormula LNT E)).
unfold E in |- *.
clear H3 E.
induction (S (codePrf x0 (notH x) x1)).
simpl in |- *.
auto.
intros.
unfold nat_rec, nat_rect in |- *.
unfold not in |- *; intros.
cut (In x2 (freeVarFormula LNN (fol.andH LNN (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n))) ((fix F (n : nat) : (fun _ : nat => fol.Formula LNN) n := match n with | O => LNT2LNN_formula (equal Zero Zero) | S n0 => (fun (n1 : nat) (rec : fol.Formula LNN) => fol.andH LNN (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n1))) rec) n0 (F n0) end) n)))).
clear H3.
intros.
SimplFreeVar.
apply (le_not_lt x2 1).
apply (freeVarCodeSysPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR (LNT2LNN_formula repT) v0 freeVarRepT').
apply H4.
destruct x2 as [| n0].
elim H6; reflexivity.
destruct n0.
elim H5; reflexivity.
apply lt_n_S.
apply lt_O_Sn.
rewrite <- LNT2LNN_natToTerm in H3.
rewrite LNT2LNN_freeVarTerm in H3.
apply (closedNatToTerm _ _ H3).
rewrite <- LNT2LNN_natToTerm in H3.
rewrite LNT2LNN_freeVarTerm in H3.
apply (closedNatToTerm _ _ H3).
assert (In x2 (freeVarFormula LNT (LNN2LNT_formula (nat_rec (fun _ : nat => fol.Formula LNN) (LNT2LNN_formula (equal Zero Zero)) (fun (n : nat) (rec : fol.Formula LNN) => fol.andH LNN (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n))) rec) n)))).
apply LNN2LNT_freeVarFormula2.
apply H3.
apply (IHn _ H4).
apply LNN2LNT_freeVarFormula1.
apply H3.
apply impE with E.
set (G := substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0 (natToTerm (codeFormula x))) 1 (natToTerm (codePrf x0 (notH x) x1))) in *.
apply impE with G.
apply sysExtend with PA.
assumption.
repeat apply impI.
apply forallI.
unfold not in |- *; intros.
induction H5 as (x2, H5); induction H5 as (H5, H6).
induction H6 as [x2 H6| x2 H6].
induction H6 as [x2 H6| x2 H6].
apply (closedPA 1).
exists x2.
auto.
induction H6.
unfold G in H5.
SimplFreeVar.
induction H6.
apply (H4 _ H5).
rewrite (subFormulaImp LNT).
rewrite (subFormulaExist LNT).
induction (eq_nat_dec 2 0).
discriminate a.
induction (In_dec eq_nat_dec 2 (freeVarTerm LNT (natToTermLNT (code.codeFormula LNT codeLNTFunction codeLNTRelation x)))).
elim (closedNatToTerm _ _ a).
clear b0 b.
rewrite (subFormulaAnd LNT).
apply impE with (fol.impH LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrf) 0 (natToTermLNT (code.codeFormula LNT codeLNTFunction codeLNTRelation x))) (fol.existH LNT 2 (fol.andH LNT (LNN2LNT_formula (LNN.LT (fol.var LNN 2) (fol.var LNN 1))) (substituteFormula LNT (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 1 (fol.var LNN 2))) 0 (natToTermLNT (code.codeFormula LNT codeLNTFunction codeLNTRelation x)))))).
repeat simple apply sysWeaken.
apply iffE1.
apply (reduceImp LNT).
apply iffRefl.
apply (reduceExist LNT).
apply closedPA.
apply (reduceAnd LNT).
apply iffTrans with (LNN2LNT_formula (substituteFormula LNN (LNN.LT (fol.var LNN 2) (fol.var LNN 1)) 0 (natToTermLNN (code.codeFormula LNT codeLNTFunction codeLNTRelation x)))).
rewrite <- LNN2LNT_iff.
apply NN2PA.
apply (folLogic.iffRefl LNN).
rewrite <- LNN2LNT_natToTerm.
apply LNN2LNT_subFormula.
apply iffRefl.
apply orE with (LNN2LNT_formula (fol.orH LNN (LNN.LT (fol.var LNN 1) (natToTermLNN (codePrf x0 (notH x) x1))) (LNT2LNN_formula (equal (var 1) (natToTerm (codePrf x0 (notH x) x1)))))) (LNN2LNT_formula (LNN.LT (natToTermLNN (codePrf x0 (notH x) x1)) (fol.var LNN 1))).
repeat simple apply sysWeaken.
apply impE with (LNN2LNT_formula (fol.orH LNN (LNN.LT (fol.var LNN 1) (natToTermLNN (codePrf x0 (notH x) x1))) (fol.orH LNN (LNT2LNN_formula (equal (var 1) (natToTerm (codePrf x0 (notH x) x1)))) (LNN.LT (natToTermLNN (codePrf x0 (notH x) x1)) (fol.var LNN 1))))).
repeat rewrite LNN2LNT_or.
apply impI.
apply orSys.
apply orI1.
apply orI1.
apply Axm; right; constructor.
apply orSys.
apply orI1.
apply orI2.
apply Axm; right; constructor.
apply orI2.
apply Axm; right; constructor.
apply NN2PA.
simpl in |- *.
rewrite LNT2LNN_natToTerm.
apply nn9.
apply impI.
apply impE with G.
apply impE with E.
apply impE with (LNN2LNT_formula (LNN.LT (fol.var LNN 1) (natToTermLNN (S (codePrf x0 (notH x) x1))))).
repeat simple apply sysWeaken.
apply PAboundedLT.
intros.
repeat rewrite (subFormulaImp LNT).
repeat apply impI.
fold codeFormula in |- *.
apply contradiction with (substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrf) 0 (natToTermLNT (codeFormula x))) 1 (natToTerm n)).
apply Axm; right; constructor.
apply sysWeaken.
apply impE with E.
repeat simple apply sysWeaken.
apply impI.
clear H3 H4.
induction (S (codePrf x0 (notH x) x1)).
elim (lt_n_O _ H5).
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)).
unfold E in |- *.
apply impE with (LNN2LNT_formula (nat_rec (fun _ : nat => fol.Formula LNN) (LNT2LNN_formula (equal Zero Zero)) (fun (n1 : nat) (rec : fol.Formula LNN) => fol.andH LNN (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n1))) rec) n0)).
apply sysWeaken.
repeat apply impI.
apply IHn0.
assumption.
unfold nat_rec, nat_rect in |- *.
rewrite LNN2LNT_and.
eapply andE2.
apply Axm; right; constructor.
unfold E in |- *.
unfold nat_rec, nat_rect in |- *.
rewrite H3.
rewrite LNN2LNT_and.
apply impE with (LNN2LNT_formula (fol.notH LNN (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n0)))).
apply sysWeaken.
apply iffE1.
apply iffTrans with (notH (LNN2LNT_formula (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN n0)))).
apply iffRefl.
apply (reduceNot LNT).
repeat rewrite <- LNN2LNT_natToTerm.
apply iffTrans with (substituteFormula LNT (LNN2LNT_formula (substituteFormula LNN codeSysPrf 0 (natToTermLNN (codeFormula x)))) 1 (LNN2LNT_term (natToTermLNN n0))).
apply LNN2LNT_subFormula.
apply (reduceSub LNT).
apply closedPA.
apply LNN2LNT_subFormula.
eapply andE1.
apply Axm; right; constructor.
apply impE with (substituteFormula LNT E 1 (natToTerm n)).
apply iffE1.
apply (subFormulaNil LNT).
apply H4.
apply Axm; left; right; constructor.
apply impE with (LNN2LNT_formula (fol.orH LNN (LNN.LT (fol.var LNN 1) (natToTermLNN (codePrf x0 (notH x) x1))) (LNT2LNN_formula (equal (var 1) (natToTerm (codePrf x0 (notH x) x1)))))).
repeat simple apply sysWeaken.
replace (impH (LNN2LNT_formula (fol.orH LNN (LNN.LT (fol.var LNN 1) (natToTermLNN (codePrf x0 (notH x) x1))) (LNT2LNN_formula (equal (var 1) (natToTerm (codePrf x0 (notH x) x1)))))) (LNN2LNT_formula (LNN.LT (fol.var LNN 1) (natToTermLNN (S (codePrf x0 (notH x) x1)))))) with (LNN2LNT_formula (fol.impH LNN (fol.orH LNN (LNN.LT (fol.var LNN 1) (natToTermLNN (codePrf x0 (notH x) x1))) (LNT2LNN_formula (equal (var 1) (natToTerm (codePrf x0 (notH x) x1))))) (LNN.LT (fol.var LNN 1) (natToTermLNN (S (codePrf x0 (notH x) x1)))))).
apply NN2PA.
simpl in |- *.
rewrite LNT2LNN_natToTerm.
apply nnPlusNotNeeded.
reflexivity.
apply Axm; right; constructor.
apply Axm; left; right; constructor.
apply Axm; do 2 left; right; constructor.
repeat apply impI.
apply sysWeaken.
apply existI with (natToTerm (codePrf x0 (notH x) x1)).
rewrite (subFormulaAnd LNT).
apply andI.
apply impE with (LNN2LNT_formula (LNN.LT (natToTermLNN (codePrf x0 (notH x) x1)) (fol.var LNN 1))).
repeat simple apply sysWeaken.
apply impTrans with (LNN2LNT_formula (substituteFormula LNN (LNN.LT (fol.var LNN 2) (fol.var LNN 1)) 2 (natToTermLNN (codePrf x0 (notH x) x1)))).
replace (impH (LNN2LNT_formula (LNN.LT (natToTermLNN (codePrf x0 (notH x) x1)) (fol.var LNN 1))) (LNN2LNT_formula (substituteFormula LNN (LNN.LT (fol.var LNN 2) (fol.var LNN 1)) 2 (natToTermLNN (codePrf x0 (notH x) x1))))) with (LNN2LNT_formula (fol.impH LNN (LNN.LT (natToTermLNN (codePrf x0 (notH x) x1)) (fol.var LNN 1)) (substituteFormula LNN (LNN.LT (fol.var LNN 2) (fol.var LNN 1)) 2 (natToTermLNN (codePrf x0 (notH x) x1))))).
apply NN2PA.
unfold LNN.LT in |- *.
apply (folLogic.impI LNN).
rewrite (subFormulaRelation LNN).
simpl in |- *.
apply (folLogic.Axm LNN); right; constructor.
reflexivity.
apply iffE1.
rewrite <- LNN2LNT_natToTerm.
apply LNN2LNT_subFormula.
apply Axm; right; constructor.
apply sysWeaken.
apply sysWeaken.
apply impE with (substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0 (natToTerm (codeFormula x))) 1 (natToTerm (codePrf x0 (notH x) x1))).
apply sysWeaken.
apply iffE2.
fold codeFormula in |- *.
apply iffTrans with (substituteFormula LNT (substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 1 (var 2)) 0 (natToTermLNT (codeFormula x))) 2 (natToTerm (codePrf x0 (notH x) x1))).
repeat (apply (reduceSub LNT); [ apply closedPA | idtac ]).
replace (var 2) with (LNN2LNT_term (fol.var LNN 2)).
apply LNN2LNT_subFormula.
reflexivity.
apply iffTrans with (substituteFormula LNT (substituteFormula LNT (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0 (natToTermLNT (codeFormula x))) 1 (var 2)) 2 (natToTerm (codePrf x0 (notH x) x1))).
repeat (apply (reduceSub LNT); [ apply closedPA | idtac ]).
apply (subFormulaExch LNT).
discriminate.
unfold not in |- *; intros; SimplFreeVar.
discriminate H6.
apply closedNatToTerm.
apply (subFormulaTrans LNT).
unfold not in |- *; intros; SimplFreeVar.
apply (le_not_lt 2 1).
apply freeVarCodeSysPrfN.
apply LNN2LNT_freeVarFormula1.
assumption.
apply lt_n_Sn.
apply Axm; right; constructor.
unfold G in |- *.
apply impE with (LNN2LNT_formula (substituteFormula LNN (substituteFormula LNN codeSysPrfNot 0 (natToTermLNN (codeFormula x))) 1 (natToTermLNN (codePrf x0 (notH x) x1)))).
apply iffE1.
repeat rewrite <- LNN2LNT_natToTerm.
apply iffTrans with (substituteFormula LNT (LNN2LNT_formula (substituteFormula LNN codeSysPrfNot 0 (natToTermLNN (codeFormula x)))) 1 (LNN2LNT_term (natToTermLNN (codePrf x0 (notH x) x1)))).
apply LNN2LNT_subFormula.
apply sysExtend with PA.
assumption.
apply (reduceSub LNT).
apply closedPA.
apply LNN2LNT_subFormula.
apply T'prf2Tprf.
apply codeSysPrfNCorrect1.
assumption.
clear H4.
unfold E in |- *; clear E.
induction (S (codePrf x0 (notH x) x1)).
simpl in |- *.
apply eqRefl.
unfold nat_rec, nat_rect in |- *.
rewrite LNN2LNT_and.
apply andI.
induction (eq_nat_dec (checkPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR (codeFormula x) n) 0).
unfold codeSysPrf, codeFormula in |- *.
apply T'prf2Tprf.
apply codeSysPrfCorrect3.
unfold not in |- *; intros.
rewrite H4 in a.
rewrite (checkPrfCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTRIsCorrect1) in a.
discriminate a.
decompose record (checkPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2 codeArityLNTRIsCorrect1 codeArityLNTRIsCorrect2 codeLNTFunctionInj codeLNTRelationInj _ _ b).
rewrite <- H6.
assert (x2 = x).
eapply (codeFormulaInj LNT).
apply codeLNTFunctionInj.
apply codeLNTRelationInj.
assumption.
rewrite <- H4.
apply T'prf2Tprf.
apply codeSysPrfCorrect2.
rewrite <- H4 in H3.
apply H3 with x4.
rewrite <- H6.
apply lt_n_Sn.
apply IHn.
intros.
eapply H3.
apply lt_S.
apply H4.
reflexivity.
apply impE with (notH x).
apply cp2.
apply iffE2.
apply sysExtend with PA.
apply extendsPA.
assumption.
assumption.

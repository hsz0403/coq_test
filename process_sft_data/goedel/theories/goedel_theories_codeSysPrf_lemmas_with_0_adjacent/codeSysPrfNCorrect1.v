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

Lemma codeSysPrfNCorrect1 : forall (f : fol.Formula L) (A : fol.Formulas L) (p : Prf L A (fol.notH L f)), (forall g : fol.Formula L, In g A -> mem _ U g) -> SysPrf T (substituteFormula LNN (substituteFormula LNN codeSysPrfNot 0 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm (codePrf L codeF codeR A (fol.notH L f) p))).
Proof.
intros.
unfold codeSysPrfNot in |- *.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec 2 0).
discriminate a.
induction (In_dec eq_nat_dec 2 (freeVarTerm LNN (natToTerm (codeFormula L codeF codeR f)))).
elim (closedNatToTerm _ _ a).
clear b b0.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec 2 1).
discriminate a.
induction (In_dec eq_nat_dec 2 (freeVarTerm LNN (natToTerm (codePrf L codeF codeR A (fol.notH L f) p)))).
elim (closedNatToTerm _ _ a).
clear b b0.
apply existI with (natToTerm (codeFormula L codeF codeR (fol.notH L f))).
repeat rewrite (subFormulaAnd LNN).
apply andI.
apply impE with (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTerm (codeFormula L codeF codeR (fol.notH L f)))) 1 (natToTerm (codePrf L codeF codeR A (fol.notH L f) p))).
apply sysExtend with NN.
apply TextendsNN.
apply iffE2.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (var 2)) 1 (natToTerm (codePrf L codeF codeR A (fol.notH L f) p))) 2 (natToTerm (codeFormula L codeF codeR (fol.notH L f)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H0).
apply (In_list_remove2 _ _ _ _ _ H1).
reflexivity.
simpl in H1.
decompose sum H1.
discriminate H2.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (var 2)) 2 (natToTerm (codeFormula L codeF codeR (fol.notH L f)))) 1 (natToTerm (codePrf L codeF codeR A (fol.notH L f) p))).
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
apply closedNatToTerm.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
elim (le_not_lt 2 1).
apply freeVarCodeSysPrf.
eapply In_list_remove1.
apply H0.
eapply lt_n_S.
apply lt_O_Sn.
apply codeSysPrfCorrect1.
assumption.
apply sysExtend with NN.
apply TextendsNN.
set (B := primRecFormula 1 (proj1_sig codeNotIsPR)) in *.
assert (rep : Representable NN 1 codeNot B).
unfold B in |- *; apply primRecRepresentable.
apply impE with (substituteFormula LNN (substituteFormula LNN B 1 (natToTerm (codeFormula L codeF codeR f))) 0 (natToTerm (codeFormula L codeF codeR (fol.notH L f)))).
apply iffE2.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 0 (var 2)) 1 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm (codePrf L codeF codeR A (fol.notH L f) p))) 2 (natToTerm (codeFormula L codeF codeR (fol.notH L f)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In 0 (freeVarFormula LNN (substituteFormula LNN B 0 (var 2)))).
eapply In_list_remove1.
apply H0.
induction (freeVarSubFormula3 _ _ _ _ _ H1).
elim (In_list_remove2 _ _ _ _ _ H2).
reflexivity.
induction H2 as [H2| H2].
discriminate H2.
apply H2.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 0 (var 2)) 1 (natToTerm (codeFormula L codeF codeR f))) 2 (natToTerm (codeFormula L codeF codeR (fol.notH L f)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H0).
elim (In_list_remove2 _ _ _ _ _ H1).
reflexivity.
elim (closedNatToTerm _ _ H1).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 1 (natToTerm (codeFormula L codeF codeR f))) 0 (var 2)) 2 (natToTerm (codeFormula L codeF codeR (fol.notH L f)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
simpl in H0.
decompose sum H0.
discriminate H1.
apply closedNatToTerm.
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In 2 (freeVarFormula LNN (substituteFormula LNN B 1 (natToTerm (codeFormula L codeF codeR f))))).
eapply In_list_remove1.
apply H0.
induction (freeVarSubFormula3 _ _ _ _ _ H1).
induction rep as (H3, H4).
apply (le_not_lt 2 1).
apply H3.
eapply In_list_remove1.
apply H2.
apply lt_n_S.
apply lt_O_Sn.
apply (closedNatToTerm _ _ H2).
induction rep as (H0, H1).
unfold RepresentableHelp in H1.
apply impE with (substituteFormula LNN (equal (var 0) (natToTerm (codeNot (codeFormula L codeF codeR f)))) 0 (natToTerm (codeFormula L codeF codeR (fol.notH L f)))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply H1.
rewrite (subFormulaEqual LNN).
rewrite (subTermVar1 LNN).
rewrite (subTermNil LNN).
rewrite (codeNotCorrect L codeF codeR).
apply eqRefl.
apply closedNatToTerm.

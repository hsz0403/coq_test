Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import folProp.
Require Import folProof.
Require Import folReplace.
Require Import folLogic3.
Require Import subProp.
Require Import ListExt.
Require Import fixPoint.
Require Import codeSysPrf.
Require Import NNtheory.
Require Import code.
Require Import PRrepresentable.
Require Import expressible.
Require Import checkPrf.
Require Import codeNatToTerm.
Section Rosser's_Incompleteness.
Definition codeFormula := codeFormula LNN codeLNTFunction codeLNNRelation.
Variable T : System.
Hypothesis extendsNN : Included _ NN T.
Variable repT : Formula.
Variable v0 : nat.
Hypothesis freeVarRepT : forall v : nat, In v (freeVarFormula LNN repT) -> v = v0.
Hypothesis expressT1 : forall f : Formula, mem _ T f -> SysPrf T (substituteFormula LNN repT v0 (natToTerm (codeFormula f))).
Hypothesis expressT2 : forall f : Formula, ~ mem _ T f -> SysPrf T (notH (substituteFormula LNN repT v0 (natToTerm (codeFormula f)))).
Definition codeSysPrf := codeSysPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0.
Definition codeSysPrfCorrect1 := codeSysPrfCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT1.
Definition codeSysPrfCorrect2 := codeSysPrfCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT2.
Definition codeSysPrfCorrect3 := codeSysPrfCorrect3 LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2 codeArityLNNRIsPR codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2 codeLNTFunctionInj codeLNNRelationInj T extendsNN.
Definition codePrf := codePrf LNN codeLNTFunction codeLNNRelation.
Definition codeSysPrfNot := codeSysPrfNot LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0.
Definition freeVarCodeSysPrfN := freeVarCodeSysPrfN LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0 freeVarRepT.
Definition codeSysPrfNCorrect1 := codeSysPrfNCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT1.
Definition codeSysPrfNCorrect2 := codeSysPrfNCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT2.
Definition codeSysPrfNCorrect3 := codeSysPrfNCorrect3 LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2 codeArityLNNRIsPR codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2 codeLNTFunctionInj codeLNNRelationInj T extendsNN repT v0 freeVarRepT.
End Rosser's_Incompleteness.
Definition RepresentsInSelf (T:System) := exists rep:Formula, exists v:nat, (forall x : nat, In x (freeVarFormula LNN rep) -> x = v) /\ (forall f : Formula, mem Formula T f -> SysPrf T (substituteFormula LNN rep v (natToTerm (codeFormula f)))) /\ (forall f : Formula, ~ mem Formula T f -> SysPrf T (notH (substituteFormula LNN rep v (natToTerm (codeFormula f))))).
Definition DecidableSet (A:_)(s:Ensemble A) := (forall x : A, mem A s x \/ ~ mem A s x).

Lemma searchProof : (forall x : Formula, mem _ T x \/ ~ mem _ T x) -> forall (a b : Formula) (A : Formulas) (p : Prf LNN A a), (exists B : Formulas, (exists q : Prf LNN B b, codePrf _ _ q < S (codePrf _ _ p) /\ (forall x : Formula, In x B -> mem _ T x))) \/ (forall (B : Formulas) (q : Prf LNN B b), codePrf _ _ q < S (codePrf _ _ p) -> exists g : Formula, In g B /\ ~ mem _ T g).
Proof.
intros.
induction (S (codePrf A a p)).
right.
intros.
elim (lt_n_O _ H0).
induction IHn as [H0| H0].
left.
decompose record H0.
exists x.
exists x0.
auto.
induction (eq_nat_dec (checkPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR (codeFormula b) n) 0).
right.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H1)).
eauto.
rewrite <- H2 in a0.
rewrite (checkPrfCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNNRIsCorrect1) in a0.
discriminate a0.
decompose record (checkPrfCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2 codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2 codeLNTFunctionInj codeLNNRelationInj _ _ b0).
assert (x = b).
eapply codeFormulaInj.
apply codeLNTFunctionInj.
apply codeLNNRelationInj.
assumption.
rewrite <- H1.
induction (decideAxioms H x0).
left.
exists x0.
exists x1.
unfold codePrf in |- *.
rewrite H3.
auto.
right.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)).
rewrite <- H1 in H0.
eauto.
assert (B = x0).
eapply (codePrfInjAxm LNN) with (p := q) (q := x1).
apply codeLNTFunctionInj.
apply codeLNNRelationInj.
transitivity n.
unfold codePrf in H6.
apply H6.
symmetry in |- *.
apply H3.
rewrite H7.
assumption.

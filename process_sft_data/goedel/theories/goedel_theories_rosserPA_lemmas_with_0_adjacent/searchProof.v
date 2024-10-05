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

Lemma searchProof : (forall x : Formula, mem _ T x \/ ~ mem _ T x) -> forall (a b : Formula) (A : Formulas) (p : Prf LNT A a), (exists B : Formulas, (exists q : Prf LNT B b, codePrf _ _ q < S (codePrf _ _ p) /\ (forall x : Formula, In x B -> mem _ T x))) \/ (forall (B : Formulas) (q : Prf LNT B b), codePrf _ _ q < S (codePrf _ _ p) -> exists g : Formula, In g B /\ ~ mem _ T g).
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
induction (eq_nat_dec (checkPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR (codeFormula b) n) 0).
right.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H1)).
eauto.
rewrite <- H2 in a0.
rewrite (checkPrfCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTRIsCorrect1) in a0.
discriminate a0.
decompose record (checkPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2 codeArityLNTRIsCorrect1 codeArityLNTRIsCorrect2 codeLNTFunctionInj codeLNTRelationInj _ _ b0).
assert (x = b).
eapply codeFormulaInj.
apply codeLNTFunctionInj.
apply codeLNTRelationInj.
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
eapply (codePrfInjAxm LNT) with (p := q) (q := x1).
apply codeLNTFunctionInj.
apply codeLNTRelationInj.
transitivity n.
unfold codePrf in H6.
apply H6.
symmetry in |- *.
apply H3.
rewrite H7.
assumption.

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

Theorem Incompleteness : forall T : System, Included Formula NN T -> RepresentsInSelf T -> DecidableSet Formula T -> exists f : Formula, (Sentence f) /\ (SysPrf T f \/ SysPrf T (notH f) -> Inconsistent LNN T).
Proof.
intros.
repeat induction H0.
apply Rosser'sIncompleteness with x x0; auto; tauto.

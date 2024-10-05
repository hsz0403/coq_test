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

Lemma extendsNN : Included _ NN T'.
Proof.
unfold Included in |- *.
intros.
unfold T' in |- *.
left.
assumption.

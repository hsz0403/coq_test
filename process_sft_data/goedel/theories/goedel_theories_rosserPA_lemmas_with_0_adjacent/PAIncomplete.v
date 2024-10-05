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

Theorem PAIncomplete : exists f : Formula, (Sentence f) /\ ~(SysPrf PA f \/ SysPrf PA (notH f)).
Proof.
assert (Expressible NN 1 codePA (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0 (natToTermLNN 1))).
apply (Representable2Expressible _ closedNN1).
simpl.
apply nn1.
apply primRecRepresentable.
induction H as (H, H0).
simpl in H0.
assert (exists f : Formula, (forall v : nat, ~ In v (freeVarFormula LNT f)) /\ (SysPrf PA f \/ SysPrf PA (notH f) -> Inconsistent LNT PA)).
eapply Rosser'sIncompleteness with (repT := LNN2LNT_formula (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0 (natToTermLNN 1))) (v0 := 1).
unfold Included in |- *.
auto.
intros.
assert (v <= 1 /\ v <> 0).
apply H.
apply LNN2LNT_freeVarFormula1.
apply H1.
destruct v as [| n].
induction H2 as (H2, H3).
elim H3.
reflexivity.
destruct n.
reflexivity.
induction H2 as (H2, H3).
elim (le_not_lt _ _ H2).
apply lt_n_S.
apply lt_O_Sn.
intros.
rewrite <- LNN2LNT_natToTerm.
eapply impE.
apply iffE1.
apply LNN2LNT_subFormula.
apply NN2PA.
assert (if codePA (codeFormula f) then LNN.SysPrf NN (substituteFormula LNN (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0 (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f))) else LNN.SysPrf NN (LNN.notH (substituteFormula LNN (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0 (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f))))).
apply H0.
clear H0.
assert (codePA (codeFormula f) = true).
apply codePAcorrect3.
assumption.
rewrite H0 in H2.
assumption.
intros.
rewrite <- LNN2LNT_natToTerm.
eapply impE with (LNN2LNT_formula (LNN.notH (substituteFormula LNN (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0 (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f))))).
simpl in |- *.
apply cp2.
apply iffE2.
apply LNN2LNT_subFormula.
apply NN2PA.
assert (if codePA (codeFormula f) then LNN.SysPrf NN (substituteFormula LNN (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0 (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f))) else LNN.SysPrf NN (LNN.notH (substituteFormula LNN (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0 (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f))))).
apply H0.
clear H0.
assert (codePA (codeFormula f) = false).
apply codePAcorrect2.
assumption.
rewrite H0 in H2.
assumption.
apply PAdec.
clear H H0.
decompose record H1.
exists x.
split.
assumption.
unfold not in |- *; intros.
unfold Inconsistent in H2.
induction PAconsistent.
auto.

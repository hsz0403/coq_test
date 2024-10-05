Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import folProp.
Require Import folProof.
Require Import subProp.
Require Import ListExt.
Require Import fixPoint.
Require Import codeSysPrf.
Require Import wConsistent.
Require Import NN.
Require Import code.
Require Import checkPrf.
Section Goedel's_1st_Incompleteness.
Definition codeFormula := codeFormula LNN codeLNTFunction codeLNNRelation.
Variable T : System.
Hypothesis extendsNN : Included _ NN T.
Variable repT : Formula.
Variable v0 : nat.
Hypothesis freeVarRepT : forall v : nat, In v (freeVarFormula LNN repT) -> v = v0.
Hypothesis expressT1 : forall f : Formula, mem _ T f -> SysPrf T (substituteFormula LNN repT v0 (natToTerm (codeFormula f))).
Hypothesis expressT2 : forall f : Formula, ~ mem _ T f -> SysPrf T (notH (substituteFormula LNN repT v0 (natToTerm (codeFormula f)))).
Definition codeSysPrf := codeSysPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0.
Definition codeSysPf := codeSysPf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0.
Definition codeSysPfCorrect := codeSysPfCorrect LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT1.
Definition codeSysPrfCorrect2 := codeSysPrfCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT2.
Definition codeSysPrfCorrect3 := codeSysPrfCorrect3 LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2 codeArityLNNRIsPR codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2 codeLNTFunctionInj codeLNNRelationInj T extendsNN.
Definition G := let (a,_) := FixPointLNN (notH codeSysPf) 0 in a.
End Goedel's_1st_Incompleteness.

Lemma FirstIncompletenessA : SysPrf T G -> Inconsistent LNN T.
Proof.
intros.
unfold G in H.
destruct (FixPointLNN (notH codeSysPf) 0) as [x [H1 H2]].
unfold Inconsistent in |- *.
intros.
apply contradiction with x.
assumption.
apply impE with (notH (substituteFormula LNN (notH codeSysPf) 0 (codeNatToTerm.natToTermLNN (code.codeFormula LNN codeLNTFunction codeLNNRelation x)))).
apply cp2.
apply iffE1.
apply sysExtend with NN.
assumption.
apply H1.
rewrite (subFormulaNot LNN).
apply nnI.
apply codeSysPfCorrect.
assumption.

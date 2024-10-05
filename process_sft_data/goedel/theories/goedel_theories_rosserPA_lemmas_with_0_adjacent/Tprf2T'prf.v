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

Lemma Tprf2T'prf : forall f : Formula, SysPrf T f -> folProof.SysPrf LNN T' (LNT2LNN_formula f).
Proof.
intros.
unfold T' in |- *.
apply (folLogic.sysExtend LNN) with (fun x : fol.Formula LNN => mem (fol.Formula LNT) T (LNN2LNT_formula x)).
unfold Included in |- *.
intros.
right.
assumption.
induction H as (x, H); induction H as (x0, H).
exists (map LNT2LNN_formula x).
induction x0 as [A| Axm1 Axm2 A B x0_1 Hrecx0_1 x0_0 Hrecx0_0| Axm A v n x0 Hrecx0| A B| A B C| A B| A v t| A v n| A B v| | | | R| f]; simpl in |- *.
exists (AXM LNN (LNT2LNN_formula A)).
intros.
unfold mem in |- *.
unfold Ensembles.In in |- *.
induction H0 as [H0| H0].
rewrite <- H0.
rewrite LNT2LNT_formula.
apply H.
auto with datatypes.
induction H0.
assert (forall g : fol.Formula LNT, In g Axm1 -> mem (fol.Formula LNT) T g).
auto with datatypes.
assert (forall g : fol.Formula LNT, In g Axm2 -> mem (fol.Formula LNT) T g).
auto with datatypes.
induction (Hrecx0_0 H1).
induction (Hrecx0_1 H0).
clear Hrecx0_0 Hrecx0_1 H0 H1.
assert (map LNT2LNN_formula (Axm1 ++ Axm2) = map LNT2LNN_formula Axm1 ++ map LNT2LNN_formula Axm2).
generalize Axm1 Axm2; intros.
induction Axm0 as [| a Axm0 HrecAxm0]; simpl in |- *.
reflexivity.
rewrite HrecAxm0.
reflexivity.
rewrite H0.
exists (MP LNN (map LNT2LNN_formula Axm1) (map LNT2LNN_formula Axm2) (LNT2LNN_formula A) (LNT2LNN_formula B) x0 x).
intros.
induction (in_app_or _ _ _ H1); auto.
induction (Hrecx0 H).
assert (~ In v (freeVarListFormula LNN (map LNT2LNN_formula Axm))).
clear x0 H Hrecx0 x H0.
unfold not in |- *; intros; apply n.
clear n.
induction Axm as [| a Axm HrecAxm].
auto.
simpl in |- *.
simpl in H.
apply in_or_app.
induction (in_app_or _ _ _ H).
left.
rewrite <- (LNT2LNT_formula a).
apply LNN2LNT_freeVarFormula2.
assumption.
auto.
exists (GEN LNN (map LNT2LNN_formula Axm) (LNT2LNN_formula A) v H1 x).
auto.
exists (IMP1 LNN (LNT2LNN_formula A) (LNT2LNN_formula B)).
tauto.
exists (IMP2 LNN (LNT2LNN_formula A) (LNT2LNN_formula B) (LNT2LNN_formula C)).
tauto.
exists (CP LNN (LNT2LNN_formula A) (LNT2LNN_formula B)).
tauto.
rewrite LNT2LNN_subFormula.
exists (FA1 LNN (LNT2LNN_formula A) v (LNT2LNN_term t)).
tauto.
rewrite <- LNT2LNN_freeVarFormula in n.
exists (FA2 LNN (LNT2LNN_formula A) v n).
tauto.
exists (FA3 LNN (LNT2LNN_formula A) (LNT2LNN_formula B) v).
tauto.
exists (EQ1 LNN).
tauto.
exists (EQ2 LNN).
tauto.
exists (EQ3 LNN).
tauto.
induction R.
induction f; simpl in |- *.
exists (EQ5 LNN Languages.Plus).
tauto.
exists (EQ5 LNN Languages.Times).
tauto.
exists (EQ5 LNN Languages.Succ).
tauto.
exists (EQ5 LNN Languages.Zero).
tauto.

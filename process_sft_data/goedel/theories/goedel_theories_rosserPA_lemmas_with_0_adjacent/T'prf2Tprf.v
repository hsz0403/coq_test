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

Lemma T'prf2Tprf : forall f : fol.Formula LNN, folProof.SysPrf LNN T' f -> SysPrf T (LNN2LNT_formula f).
Proof.
assert (freeVarPA : forall x : Formulas, (forall g : fol.Formula LNT, In g x -> mem (fol.Formula LNT) PA g) -> forall v : nat, In v (freeVarListFormula LNT x) -> False).
intros.
induction x as [| a x Hrecx].
apply H0.
simpl in H0.
induction (in_app_or _ _ _ H0).
apply (closedPA v).
exists a.
auto with datatypes.
auto with datatypes.
intros.
induction H as (x, H); induction H as (x0, H).
unfold SysPrf, folProof.SysPrf in |- *.
assert (exists Axm : fol.Formulas LNT, (forall v : nat, In v (freeVarListFormula _ Axm) -> In v (freeVarListFormula _ x)) /\ ex (fun _ : Prf LNT Axm (LNN2LNT_formula f) => forall g : fol.Formula LNT, In g Axm -> mem (fol.Formula LNT) T g)).
induction x0 as [A| Axm1 Axm2 A B x0_1 Hrecx0_1 x0_0 Hrecx0_0| Axm A v n x0 Hrecx0| A B| A B C| A B| A v t| A v n| A B v| | | | R| f]; simpl in |- *.
assert (mem (fol.Formula LNN) T' A).
auto with datatypes.
repeat induction H0.
exists (PA1 :: nil).
split.
auto.
exists (AXM _ PA1).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
exists (PA2 :: nil).
split.
auto.
exists (AXM _ PA2).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
exists (PA3 :: nil).
split.
auto.
exists (AXM _ PA3).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
exists (PA4 :: nil).
split.
auto.
exists (AXM _ PA4).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
exists (PA5 :: nil).
split.
auto.
exists (AXM _ PA5).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
exists (PA6 :: nil).
split.
auto.
exists (AXM _ PA6).
intros.
apply extendsPA.
induction H0 as [H0| H0].
rewrite <- H0.
repeat (right; constructor) || left.
elim H0.
assert (SysPrf PA (LNN2LNT_formula NN7)).
apply NN72PA.
induction H0 as (x, H0); induction H0 as (x0, H0).
exists x.
split.
intros.
apply (freeVarPA x H0 v H1).
exists x0.
intros.
apply extendsPA.
fold mem.
auto.
assert (SysPrf PA (LNN2LNT_formula NN8)).
apply NN82PA.
induction H0 as (x, H0); induction H0 as (x0, H0).
exists x.
split.
intros.
apply (freeVarPA x H0 v H1).
exists x0.
intros.
apply extendsPA.
fold mem.
auto.
assert (SysPrf PA (LNN2LNT_formula NN9)).
apply NN92PA.
induction H0 as (x, H0); induction H0 as (x0, H0).
exists x.
split.
intros.
apply (freeVarPA x H0 v H1).
exists x0.
intros.
apply extendsPA.
fold mem.
auto.
exists (LNN2LNT_formula x :: nil).
split.
simpl in |- *.
repeat rewrite <- app_nil_end.
apply (LNN2LNT_freeVarFormula1 x).
exists (AXM _ (LNN2LNT_formula x)).
intros.
induction H1 as [H1| H1].
unfold mem in H0.
unfold Ensembles.In in H0.
rewrite H1 in H0.
apply H0.
elim H1.
assert (forall g : fol.Formula LNN, In g Axm1 -> mem (fol.Formula LNN) T' g).
auto with datatypes.
assert (forall g : fol.Formula LNN, In g Axm2 -> mem (fol.Formula LNN) T' g).
auto with datatypes.
induction (Hrecx0_1 H0).
induction (Hrecx0_0 H1).
induction H2 as (H2, H4).
induction H3 as (H3, H5).
induction H4 as (x1, H4).
induction H5 as (x2, H5).
clear Hrecx0_1 H0 Hrecx0_0 H1.
exists (x ++ x0).
split.
repeat rewrite freeVarListFormulaApp.
intros.
induction (in_app_or _ _ _ H0); auto with datatypes.
simpl in x1.
exists (MP _ _ _ _ _ x1 x2).
intros.
induction (in_app_or _ _ _ H0); auto.
assert (forall g : fol.Formula LNN, In g Axm -> mem (fol.Formula LNN) T' g).
auto.
induction (Hrecx0 H0).
clear Hrecx0 H0.
induction H1 as (H0, H1).
induction H1 as (x1, H1).
exists x.
split.
assumption.
assert (~ In v (freeVarListFormula LNT x)).
auto.
exists (GEN _ _ _ _ H2 x1).
assumption.
exists (nil (A:=Formula)).
split.
auto.
exists (IMP1 _ (LNN2LNT_formula A) (LNN2LNT_formula B)).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (IMP2 _ (LNN2LNT_formula A) (LNN2LNT_formula B) (LNN2LNT_formula C)).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (CP _ (LNN2LNT_formula A) (LNN2LNT_formula B)).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
assert (SysPrf (Empty_set _) (impH (forallH v (LNN2LNT_formula A)) (LNN2LNT_formula (substituteFormula LNN A v t)))).
apply impTrans with (substituteFormula LNT (LNN2LNT_formula A) v (LNN2LNT_term t)).
apply impI.
apply forallE.
apply Axm; right; constructor.
apply iffE2.
apply LNN2LNT_subFormula.
induction H0 as (x, H0).
induction H0 as (x0, H0).
induction x as [| a x Hrecx].
exists x0.
simpl in |- *; tauto.
assert (mem (fol.Formula LNT) (Empty_set (fol.Formula LNT)) a).
auto with datatypes.
induction H1.
exists (nil (A:=Formula)).
split.
auto.
assert (~ In v (freeVarFormula LNT (LNN2LNT_formula A))).
unfold not in |- *; intros; apply n.
apply LNN2LNT_freeVarFormula1.
assumption.
exists (FA2 _ (LNN2LNT_formula A) v H0).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (FA3 _ (LNN2LNT_formula A) (LNN2LNT_formula B) v).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (EQ1 LNT).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (EQ2 LNT).
simpl in |- *; tauto.
exists (nil (A:=Formula)).
split.
auto.
exists (EQ3 LNT).
simpl in |- *; tauto.
assert (SysPrf (Empty_set Formula) (LNN2LNT_formula (AxmEq4 LNN R))).
apply translateProof with (Empty_set (fol.Formula LNN)).
unfold ClosedSystem in |- *.
intros.
induction H0.
intros.
induction H0.
exists (nil (A:=fol.Formula LNN)).
exists (EQ4 LNN R).
simpl in |- *; tauto.
induction H0 as (x, H0).
induction H0 as (x0, H0).
exists x.
split.
intros.
induction (In_freeVarListFormulaE _ _ _ H1).
induction H2 as (H2, H3).
assert (mem (fol.Formula LNT) (Empty_set Formula) x1).
auto.
induction H4.
exists x0.
intros.
assert (mem (fol.Formula LNT) (Empty_set Formula) g).
auto.
induction H2.
assert (SysPrf (Empty_set Formula) (LNN2LNT_formula (AxmEq5 LNN f))).
apply translateProof with (Empty_set (fol.Formula LNN)).
unfold ClosedSystem in |- *.
intros.
induction H0.
intros.
induction H0.
exists (nil (A:=fol.Formula LNN)).
exists (EQ5 LNN f).
simpl in |- *; tauto.
induction H0 as (x, H0).
induction H0 as (x0, H0).
exists x.
split.
intros.
induction (In_freeVarListFormulaE _ _ _ H1).
induction H2 as (H2, H3).
assert (mem (fol.Formula LNT) (Empty_set Formula) x1).
auto.
induction H4.
exists x0.
intros.
assert (mem (fol.Formula LNT) (Empty_set Formula) g).
auto.
induction H2.
induction H0 as (x1, H0).
induction H0 as (H0, H1).
exists x1.
assumption.

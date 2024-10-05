Require Import primRec.
Require Import cPair.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import Arith.
Require Export codeList.
Require Import folProp.
Require Import code.
Section Code_Free_Vars.
Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.
Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Let equal := equal L.
Let atomic := atomic L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Let orH := orH L.
Let andH := andH L.
Let existH := existH L.
Let iffH := iffH L.
Let ifThenElseH := ifThenElseH L.
Definition codeFreeVarTermTerms : nat -> nat := evalStrongRec 0 (fun t recs : nat => cPair (switchPR (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) (S (cPair (cPairPi2 t) 0))) (switchPR t (codeApp (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs))) 0)).
Definition codeFreeVarTerm (t : nat) : nat := cPairPi1 (codeFreeVarTermTerms t).
Definition codeFreeVarTerms (t : nat) : nat := cPairPi2 (codeFreeVarTermTerms t).
Definition codeFreeVarFormula : nat -> nat := evalStrongRec 0 (fun f recs : nat => switchPR (cPairPi1 f) (switchPR (pred (cPairPi1 f)) (switchPR (pred (pred (cPairPi1 f))) (switchPR (pred (pred (pred (cPairPi1 f)))) (codeFreeVarTerms (cPairPi2 f)) (codeListRemove (cPairPi1 (cPairPi2 f)) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))) (codeNth (f - S (cPairPi2 f)) recs)) (codeApp (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))) (codeApp (codeFreeVarTerm (cPairPi1 (cPairPi2 f))) (codeFreeVarTerm (cPairPi2 (cPairPi2 f))))).
Definition codeFreeVarListFormula : nat -> nat := evalStrongRec 0 (fun l recs : nat => switchPR l (codeApp (codeFreeVarFormula (cPairPi1 (pred l))) (codeNth (l - S (cPairPi2 (pred l))) recs)) 0).
End Code_Free_Vars.

Lemma codeFreeVarFormulaCorrect : forall f : Formula, codeFreeVarFormula (codeFormula L codeF codeR f) = codeList (freeVarFormula L f).
Proof.
intros.
set (g := fun f recs : nat => switchPR (cPairPi1 f) (switchPR (pred (cPairPi1 f)) (switchPR (pred (pred (cPairPi1 f))) (switchPR (pred (pred (pred (cPairPi1 f)))) (codeFreeVarTerms (cPairPi2 f)) (codeListRemove (cPairPi1 (cPairPi2 f)) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))) (codeNth (f - S (cPairPi2 f)) recs)) (codeApp (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))) (codeApp (codeFreeVarTerm (cPairPi1 (cPairPi2 f))) (codeFreeVarTerm (cPairPi2 (cPairPi2 f))))) in *.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf].
simpl in |- *.
rewrite <- codeAppCorrect.
repeat rewrite <- codeFreeVarTermCorrect.
generalize (codeTerm L codeF t) (codeTerm L codeF t0).
clear t t0.
intros.
unfold codeFreeVarFormula in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
simpl in |- *.
reflexivity.
simpl in |- *.
rewrite <- codeFreeVarTermsCorrect.
generalize (codeTerms L codeF (arity L (inl (Functions L) r)) t).
clear t.
intros.
unfold codeFreeVarFormula in |- *.
unfold evalStrongRec in |- *.
unfold evalStrongRecHelp in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
unfold evalPrimRecFunc in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
simpl in |- *.
rewrite <- codeAppCorrect.
rewrite <- Hrecf1.
rewrite <- Hrecf0.
clear Hrecf0 Hrecf1.
unfold codeFreeVarFormula in |- *.
fold g in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite (evalStrongRecHelp1 g (cPair 1 (cPair (codeFormula L codeF codeR f1) (codeFormula L codeF codeR f0))) (codeFormula L codeF codeR f1)).
rewrite (evalStrongRecHelp1 g (cPair 1 (cPair (codeFormula L codeF codeR f1) (codeFormula L codeF codeR f0))) (codeFormula L codeF codeR f0)).
simpl in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
eapply lt_le_trans.
apply cPairLt2.
apply cPairLe3.
apply le_n.
apply cPairLe2.
eapply lt_le_trans.
apply cPairLt2.
apply cPairLe3.
apply le_n.
apply cPairLe1.
simpl in |- *.
rewrite <- Hrecf.
clear Hrecf.
generalize (codeFormula L codeF codeR f).
clear f.
intros.
unfold codeFreeVarFormula at 1 in |- *.
fold g in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold evalComposeFunc in |- *.
unfold compose2 in |- *.
unfold evalList in |- *.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite (evalStrongRecHelp1 g (cPair 2 n) n).
simpl in |- *.
reflexivity.
apply cPairLt2.
simpl in |- *.
rewrite <- codeListRemoveCorrect.
rewrite <- Hrecf.
generalize (codeFormula L codeF codeR f).
clear Hrecf f.
intros.
unfold codeFreeVarFormula at 1 in |- *.
fold g in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
unfold evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold evalComposeFunc in |- *.
unfold compose2 in |- *.
unfold evalList in |- *.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite (evalStrongRecHelp1 g (cPair 3 (cPair n n0)) n0).
simpl in |- *.
reflexivity.
eapply lt_le_trans.
apply cPairLt2.
apply cPairLe3.
apply le_n.
apply cPairLe2.

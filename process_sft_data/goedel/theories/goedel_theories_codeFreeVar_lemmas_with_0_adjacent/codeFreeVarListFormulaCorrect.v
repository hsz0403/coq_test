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

Lemma codeFreeVarListFormulaCorrect : forall l : list Formula, codeFreeVarListFormula (codeList (map (codeFormula L codeF codeR) l)) = codeList (freeVarListFormula L l).
Proof.
intros.
unfold codeFreeVarListFormula in |- *.
set (A := fun l0 recs : nat => switchPR l0 (codeApp (codeFreeVarFormula (cPairPi1 (pred l0))) (codeNth (l0 - S (cPairPi2 (pred l0))) recs)) 0) in *.
induction l as [| a l Hrecl]; unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *; rewrite computeEvalStrongRecHelp; unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
unfold A at 1 in |- *.
rewrite evalStrongRecHelp1.
simpl in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite Hrecl.
rewrite codeFreeVarFormulaCorrect.
apply codeAppCorrect.
simpl in |- *.
apply le_lt_n_Sm.
apply cPairLe2A.

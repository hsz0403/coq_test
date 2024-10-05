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

Lemma codeFreeVarListFormulaIsPR : isPR 1 codeFreeVarListFormula.
Proof.
unfold codeFreeVarListFormula in |- *.
apply evalStrongRecIsPR.
apply compose2_3IsPR with (f1 := fun l recs : nat => l) (f2 := fun l recs : nat => codeApp (codeFreeVarFormula (cPairPi1 (pred l))) (codeNth (l - S (cPairPi2 (pred l))) recs)) (f3 := fun l recs : nat => 0).
apply pi1_2IsPR.
apply compose2_2IsPR with (f := fun l recs : nat => codeFreeVarFormula (cPairPi1 (pred l))) (g := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs).
apply filter10IsPR with (g := fun l : nat => codeFreeVarFormula (cPairPi1 (pred l))).
apply compose1_1IsPR with (f := fun l : nat => cPairPi1 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
apply codeFreeVarFormulaIsPR.
apply callIsPR with (g := fun l : nat => cPairPi2 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply codeAppIsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply switchIsPR.

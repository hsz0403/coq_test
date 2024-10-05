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

Lemma codeFreeVarFormulaIsPR : isPR 1 codeFreeVarFormula.
Proof.
unfold codeFreeVarFormula in |- *.
apply evalStrongRecIsPR.
assert (isPR 1 (fun x : nat => pred (cPairPi1 x))).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
assert (isPR 1 (fun x : nat => pred (pred (cPairPi1 x)))).
apply compose1_1IsPR with (f := fun x : nat => pred (cPairPi1 x)).
auto.
apply predIsPR.
assert (isPR 1 (fun x : nat => pred (pred (pred (cPairPi1 x))))).
apply compose1_1IsPR with (f := fun x : nat => pred (pred (cPairPi1 x))).
auto.
apply predIsPR.
apply compose2_3IsPR with (f1 := fun f recs : nat => cPairPi1 f) (f2 := fun f recs : nat => switchPR (pred (cPairPi1 f)) (switchPR (pred (pred (cPairPi1 f))) (switchPR (pred (pred (pred (cPairPi1 f)))) (codeFreeVarTerms (cPairPi2 f)) (codeListRemove (cPairPi1 (cPairPi2 f)) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))) (codeNth (f - S (cPairPi2 f)) recs)) (codeApp (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))) (f3 := fun f recs : nat => codeApp (codeFreeVarTerm (cPairPi1 (cPairPi2 f))) (codeFreeVarTerm (cPairPi2 (cPairPi2 f)))).
apply filter10IsPR.
apply cPairPi1IsPR.
apply compose2_3IsPR with (f1 := fun f recs : nat => pred (cPairPi1 f)) (f2 := fun f recs : nat => switchPR (pred (pred (cPairPi1 f))) (switchPR (pred (pred (pred (cPairPi1 f)))) (codeFreeVarTerms (cPairPi2 f)) (codeListRemove (cPairPi1 (cPairPi2 f)) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))) (codeNth (f - S (cPairPi2 f)) recs)) (f3 := fun f recs : nat => codeApp (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)).
apply filter10IsPR with (g := fun x : nat => pred (cPairPi1 x)).
auto.
apply compose2_3IsPR with (f1 := fun f recs : nat => pred (pred (cPairPi1 f))) (f2 := fun f recs : nat => switchPR (pred (pred (pred (cPairPi1 f)))) (codeFreeVarTerms (cPairPi2 f)) (codeListRemove (cPairPi1 (cPairPi2 f)) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))) (f3 := fun f recs : nat => codeNth (f - S (cPairPi2 f)) recs).
apply filter10IsPR with (g := fun x : nat => pred (pred (cPairPi1 x))).
auto.
apply compose2_3IsPR with (f1 := fun f recs : nat => pred (pred (pred (cPairPi1 f)))) (f2 := fun f recs : nat => codeFreeVarTerms (cPairPi2 f)) (f3 := fun f recs : nat => codeListRemove (cPairPi1 (cPairPi2 f)) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)).
apply filter10IsPR with (g := fun x : nat => pred (pred (pred (cPairPi1 x)))).
auto.
apply filter10IsPR with (g := fun f : nat => codeFreeVarTerms (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply codeFreeVarTermsIsPR.
apply compose2_2IsPR with (f := fun f recs : nat => cPairPi1 (cPairPi2 f)) (g := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
apply filter10IsPR with (g := fun f : nat => cPairPi1 (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply compose2_2IsPR with (f := fun f recs : nat => f - S (cPairPi2 (cPairPi2 f))) (g := fun f recs : nat => recs).
apply filter10IsPR with (g := fun f : nat => f - S (cPairPi2 (cPairPi2 f))).
apply compose1_2IsPR with (f := fun f : nat => f) (f' := fun f : nat => S (cPairPi2 (cPairPi2 f))).
apply idIsPR.
apply compose1_1IsPR with (f := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply codeListRemoveIsPR.
apply switchIsPR.
apply compose2_2IsPR with (f := fun f recs : nat => f - S (cPairPi2 f)) (g := fun f recs : nat => recs).
apply filter10IsPR with (g := fun f : nat => f - S (cPairPi2 f)).
apply compose1_2IsPR with (f := fun f : nat => f) (f' := fun f : nat => S (cPairPi2 f)).
apply idIsPR.
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply switchIsPR.
apply compose2_2IsPR with (f := fun f recs : nat => codeNth (f - S (cPairPi1 (cPairPi2 f))) recs) (g := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
apply compose2_2IsPR with (f := fun f recs : nat => f - S (cPairPi1 (cPairPi2 f))) (g := fun f recs : nat => recs).
apply filter10IsPR with (g := fun f : nat => f - S (cPairPi1 (cPairPi2 f))).
apply compose1_2IsPR with (f := fun f : nat => f) (f' := fun f : nat => S (cPairPi1 (cPairPi2 f))).
apply idIsPR.
apply compose1_1IsPR with (f := fun f : nat => cPairPi1 (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply compose2_2IsPR with (f := fun f recs : nat => f - S (cPairPi2 (cPairPi2 f))) (g := fun f recs : nat => recs).
apply filter10IsPR with (g := fun f : nat => f - S (cPairPi2 (cPairPi2 f))).
apply compose1_2IsPR with (f := fun f : nat => f) (f' := fun f : nat => S (cPairPi2 (cPairPi2 f))).
apply idIsPR.
apply compose1_1IsPR with (f := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply codeAppIsPR.
apply switchIsPR.
apply filter10IsPR with (g := fun f : nat => codeApp (codeFreeVarTerm (cPairPi1 (cPairPi2 f))) (codeFreeVarTerm (cPairPi2 (cPairPi2 f)))).
apply compose1_2IsPR with (f := fun f : nat => codeFreeVarTerm (cPairPi1 (cPairPi2 f))) (f' := fun f : nat => codeFreeVarTerm (cPairPi2 (cPairPi2 f))).
apply compose1_1IsPR with (f := fun f : nat => cPairPi1 (cPairPi2 f)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply codeFreeVarTermIsPR.
apply compose1_1IsPR with (f := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply codeFreeVarTermIsPR.
apply codeAppIsPR.
apply switchIsPR.

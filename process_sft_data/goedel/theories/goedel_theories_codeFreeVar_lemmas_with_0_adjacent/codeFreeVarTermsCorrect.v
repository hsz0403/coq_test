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

Lemma codeFreeVarTermsCorrect : forall (n : nat) (ts : Terms n), codeFreeVarTerms (codeTerms L codeF n ts) = codeList (freeVarTerms L n ts).
Proof.
intros.
induction ts as [| n t ts Hrects].
simpl in |- *.
unfold codeTerms in |- *.
unfold codeFreeVarTerms in |- *.
unfold codeFreeVarTermTerms in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
unfold freeVarTerms in |- *.
fold (freeVarTerm L t) in |- *.
fold (freeVarTerms L n ts) in |- *.
rewrite <- codeAppCorrect.
rewrite <- Hrects.
rewrite <- codeFreeVarTermCorrect.
clear Hrects.
unfold codeTerms in |- *.
fold (codeTerm L codeF t) in |- *.
fold (codeTerms L codeF n ts) in |- *.
generalize (codeTerm L codeF t) (codeTerms L codeF n ts).
clear t ts.
intros.
unfold codeFreeVarTerms at 1 in |- *.
unfold codeFreeVarTermTerms in |- *.
unfold evalStrongRec in |- *.
set (g := fun t0 recs : nat => cPair (switchPR (cPairPi1 t0) (cPairPi2 (codeNth (t0 - S (cPairPi2 t0)) recs)) (S (cPair (cPairPi2 t0) 0))) (switchPR t0 (codeApp (cPairPi1 (codeNth (t0 - S (cPairPi1 (pred t0))) recs)) (cPairPi2 (codeNth (t0 - S (cPairPi2 (pred t0))) recs))) 0)) in *.
unfold evalComposeFunc in |- *.
unfold evalOneParamList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc in |- *.
unfold g at 1 in |- *.
rewrite (evalStrongRecHelp1 g (S (cPair n0 n1)) (cPairPi1 (pred (S (cPair n0 n1))))) .
rewrite (evalStrongRecHelp1 g (S (cPair n0 n1)) (cPairPi2 (pred (S (cPair n0 n1))))) .
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
simpl in |- *.
rewrite cPairProjections2.
apply le_lt_n_Sm.
apply cPairLe2.
simpl in |- *.
rewrite cPairProjections1.
apply le_lt_n_Sm.
apply cPairLe1.

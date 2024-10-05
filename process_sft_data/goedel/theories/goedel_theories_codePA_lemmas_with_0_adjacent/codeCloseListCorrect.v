Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import folProp.
Require Import code.
Require Import codeList.
Require Import codeFreeVar.
Require Import extEqualNat.
Require Vector.
Require Import prLogic.
Section close.
Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.
Let Formula := Formula L.
Let codeFormula := codeFormula L codeF codeR.
Definition codeCloseList : nat -> nat -> nat := evalStrongRec 1 (fun l recs f : nat => switchPR l (cPair 3 (cPair (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs))) f).
Definition codeClose (f : nat) : nat := codeCloseList (codeNoDup (codeFreeVarFormula f)) f.
End close.
Require Import PA.
Require Import codeSubFormula.
Section Code_PA.
Let codeTerm := codeTerm LNT codeLNTFunction.
Let codeFormula := codeFormula LNT codeLNTFunction codeLNTRelation.
Let codeFormulaInj := codeFormulaInj LNT codeLNTFunction codeLNTRelation codeLNTFunctionInj codeLNTRelationInj.
Definition codeOpen : nat -> nat := evalStrongRec 0 (fun f recs : nat => switchPR (cPairPi1 f) (switchPR (pred (cPairPi1 f)) (switchPR (pred (pred (cPairPi1 f))) (switchPR (pred (pred (pred (cPairPi1 f)))) f (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)) f) f) f).
Definition codeInductionSchema (f : nat) : bool := let n := cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (codeOpen f)))))) in let g := cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (codeOpen f)))))) in beq_nat (codeClose (codeImp (codeSubFormula g n (codeTerm Zero)) (codeImp (codeForall n (codeImp g (codeSubFormula g n (codeTerm (Succ (var n)))))) (codeForall n g)))) f.
Definition codePA : nat -> bool := orRel 1 (beq_nat (codeFormula PA6)) (orRel 1 (beq_nat (codeFormula PA5)) (orRel 1 (beq_nat (codeFormula PA4)) (orRel 1 (beq_nat (codeFormula PA3)) (orRel 1 (beq_nat (codeFormula PA2)) (orRel 1 (beq_nat (codeFormula PA1)) codeInductionSchema))))).
End Code_PA.

Lemma codeCloseListCorrect : forall (l : list nat) (f : Formula), codeCloseList (codeList l) (codeFormula f) = codeFormula (closeList L l f).
Proof.
intros.
set (g := fun l recs f : nat => switchPR l (cPair 3 (cPair (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs))) f) in *.
induction l as [| a l Hrecl].
simpl in |- *.
unfold codeCloseList in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
rewrite cPairProjections1.
reflexivity.
simpl in |- *.
unfold codeCloseList in |- *.
fold g in |- *.
assert (forall n m : nat, m < n -> extEqual 1 (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 g n) 0 (Vector.nil _)) (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 g m)).
intros.
apply (evalStrongRecHelp2 1).
assumption.
simpl in H.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
unfold g at 1 in |- *.
rewrite H.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
rewrite <- Hrecl.
reflexivity.
simpl in |- *.
apply le_lt_n_Sm.
apply cPairLe2A.

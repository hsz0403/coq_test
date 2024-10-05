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

Lemma codeOpenIsPR : isPR 1 codeOpen.
Proof.
unfold codeOpen in |- *.
apply evalStrongRecIsPR.
apply compose2_3IsPR with (f1 := fun f recs : nat => cPairPi1 f) (f2 := fun f recs : nat => switchPR (pred (cPairPi1 f)) (switchPR (pred (pred (cPairPi1 f))) (switchPR (pred (pred (pred (cPairPi1 f)))) f (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)) f) f) (f3 := fun f recs : nat => f).
apply filter10IsPR.
apply cPairPi1IsPR.
apply compose2_3IsPR with (f1 := fun f recs : nat => pred (cPairPi1 f)) (f2 := fun f recs : nat => switchPR (pred (pred (cPairPi1 f))) (switchPR (pred (pred (pred (cPairPi1 f)))) f (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)) f) (f3 := fun f recs : nat => f).
apply filter10IsPR with (g := fun f : nat => pred (cPairPi1 f)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply compose2_3IsPR with (f1 := fun f recs : nat => pred (pred (cPairPi1 f))) (f2 := fun f recs : nat => switchPR (pred (pred (pred (cPairPi1 f)))) f (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)) (f3 := fun f recs : nat => f).
apply filter10IsPR with (g := fun f : nat => pred (pred (cPairPi1 f))).
apply compose1_1IsPR with (f := fun f : nat => pred (cPairPi1 f)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply predIsPR.
apply compose2_3IsPR with (f1 := fun f recs : nat => pred (pred (pred (cPairPi1 f)))) (f2 := fun f recs : nat => f) (f3 := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
apply filter10IsPR with (g := fun f : nat => pred (pred (pred (cPairPi1 f)))).
apply compose1_1IsPR with (f := fun f : nat => pred (pred (cPairPi1 f))).
apply compose1_1IsPR with (f := fun f : nat => pred (cPairPi1 f)).
apply compose1_1IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply predIsPR.
apply predIsPR.
apply pi1_2IsPR.
apply callIsPR with (g := fun f : nat => cPairPi2 (cPairPi2 f)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply switchIsPR.
apply pi1_2IsPR.
apply switchIsPR.
apply pi1_2IsPR.
apply switchIsPR.
apply pi1_2IsPR.
apply switchIsPR.

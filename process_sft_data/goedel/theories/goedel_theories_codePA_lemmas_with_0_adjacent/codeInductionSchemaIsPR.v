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

Lemma codeInductionSchemaIsPR : isPRrel 1 codeInductionSchema.
Proof.
lazy beta delta [codeInductionSchema] in |- *.
set (A := fun f : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (codeOpen f)))))) in *.
assert (isPR 1 A).
unfold A in |- *.
apply compose1_1IsPR with (g := iterate cPairPi2 5) (f := codeOpen).
apply codeOpenIsPR.
apply iterateIsPR.
apply cPairPi2IsPR.
assert (isPRrel 1 (fun f : nat => let n := cPairPi1 (A f) in let g := cPairPi2 (A f) in beq_nat (codeClose (codeImp (codeSubFormula g n (codeTerm Zero)) (codeImp (codeForall n (codeImp g (codeSubFormula g n (codeTerm (Succ (var n)))))) (codeForall n g)))) f)).
unfold isPRrel in |- *.
apply compose1_2IsPR with (g := charFunction 2 beq_nat) (f' := fun f : nat => f) (f := fun f : nat => codeClose (codeImp (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm Zero)) (codeImp (codeForall (cPairPi1 (A f)) (codeImp (cPairPi2 (A f)) (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm (Succ (var (cPairPi1 (A f)))))))) (codeForall (cPairPi1 (A f)) (cPairPi2 (A f)))))).
apply compose1_1IsPR with (f := fun f : nat => codeImp (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm Zero)) (codeImp (codeForall (cPairPi1 (A f)) (codeImp (cPairPi2 (A f)) (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm (Succ (var (cPairPi1 (A f)))))))) (codeForall (cPairPi1 (A f)) (cPairPi2 (A f))))).
apply compose1_2IsPR with (f := fun f : nat => codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm Zero)) (f' := fun f : nat => codeImp (codeForall (cPairPi1 (A f)) (codeImp (cPairPi2 (A f)) (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm (Succ (var (cPairPi1 (A f)))))))) (codeForall (cPairPi1 (A f)) (cPairPi2 (A f)))).
apply compose1_3IsPR with (f1 := fun f : nat => cPairPi2 (A f)) (f2 := fun f : nat => cPairPi1 (A f)) (f3 := fun f : nat => codeTerm Zero).
apply compose1_1IsPR.
assumption.
apply cPairPi2IsPR.
apply compose1_1IsPR.
assumption.
apply cPairPi1IsPR.
apply const1_NIsPR.
apply codeSubFormulaIsPR.
apply compose1_2IsPR with (f := fun f : nat => codeForall (cPairPi1 (A f)) (codeImp (cPairPi2 (A f)) (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm (Succ (var (cPairPi1 (A f)))))))) (f' := fun f : nat => codeForall (cPairPi1 (A f)) (cPairPi2 (A f))).
apply compose1_2IsPR with (f := fun f : nat => cPairPi1 (A f)) (f' := fun f : nat => codeImp (cPairPi2 (A f)) (codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm (Succ (var (cPairPi1 (A f))))))).
apply compose1_1IsPR.
assumption.
apply cPairPi1IsPR.
apply compose1_2IsPR with (f := fun f : nat => cPairPi2 (A f)) (f' := fun f : nat => codeSubFormula (cPairPi2 (A f)) (cPairPi1 (A f)) (codeTerm (Succ (var (cPairPi1 (A f)))))).
apply compose1_1IsPR.
assumption.
apply cPairPi2IsPR.
apply compose1_3IsPR with (f1 := fun f : nat => cPairPi2 (A f)) (f2 := fun f : nat => cPairPi1 (A f)) (f3 := fun f : nat => codeTerm (Succ (var (cPairPi1 (A f))))).
apply compose1_1IsPR.
assumption.
apply cPairPi2IsPR.
apply compose1_1IsPR.
assumption.
apply cPairPi1IsPR.
assert (isPR 1 (fun f : nat => cPair 3 (S (cPair (cPair 0 (cPairPi1 (A f))) 0)))).
apply compose1_2IsPR with (f := fun f : nat => 3) (f' := fun f : nat => S (cPair (cPair 0 (cPairPi1 (A f))) 0)).
apply const1_NIsPR.
apply compose1_1IsPR with (f := fun f : nat => cPair (cPair 0 (cPairPi1 (A f))) 0).
apply compose1_2IsPR with (f := fun f : nat => cPair 0 (cPairPi1 (A f))) (f' := fun f : nat => 0).
apply compose1_2IsPR with (f := fun f : nat => 0) (f' := fun f : nat => cPairPi1 (A f)).
apply const1_NIsPR.
apply compose1_1IsPR.
assumption.
apply cPairPi1IsPR.
apply cPairIsPR.
apply const1_NIsPR.
apply cPairIsPR.
apply succIsPR.
apply cPairIsPR.
induction H0 as (x, p).
exists x.
eapply extEqualTrans.
apply p.
simpl in |- *.
intros.
reflexivity.
apply codeSubFormulaIsPR.
apply codeImpIsPR.
apply codeForallIsPR.
apply compose1_2IsPR with (f := fun f : nat => cPairPi1 (A f)) (f' := fun f : nat => cPairPi2 (A f)).
apply compose1_1IsPR.
assumption.
apply cPairPi1IsPR.
apply compose1_1IsPR.
assumption.
apply cPairPi2IsPR.
apply codeForallIsPR.
apply codeImpIsPR.
apply codeImpIsPR.
apply codeCloseIsPR.
apply idIsPR.
apply eqIsPR.
apply H0.

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

Lemma codeInductionSchemaCorrect1 : forall f : Formula, InductionSchema f -> codeInductionSchema (codeFormula f) = true.
Proof.
intros.
induction H as (x, H).
induction H as (x0, H).
unfold PA7 in H.
rewrite H.
clear H f.
lazy beta delta [codeInductionSchema] in |- *.
rewrite codeOpenCorrect.
replace (open (close LNT (impH (substituteFormula LNT x x0 Zero) (impH (forallH x0 (impH x (substituteFormula LNT x x0 (Succ (var x0))))) (forallH x0 x))))) with (impH (substituteFormula LNT x x0 Zero) (impH (forallH x0 (impH x (substituteFormula LNT x x0 (Succ (var x0))))) (forallH x0 x))).
replace (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (codeFormula (impH (substituteFormula LNT x x0 Zero) (impH (forallH x0 (impH x (substituteFormula LNT x x0 (Succ (var x0))))) (forallH x0 x)))))))))) with x0.
replace (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 (codeFormula (impH (substituteFormula LNT x x0 Zero) (impH (forallH x0 (impH x (substituteFormula LNT x x0 (Succ (var x0))))) (forallH x0 x)))))))))) with (codeFormula x).
cbv zeta in |- *.
unfold codeFormula in |- *.
rewrite <- codeCloseCorrect.
replace (codeClose (codeImp (codeSubFormula (code.codeFormula LNT codeLNTFunction codeLNTRelation x) x0 (codeTerm Zero)) (codeImp (codeForall x0 (codeImp (code.codeFormula LNT codeLNTFunction codeLNTRelation x) (codeSubFormula (code.codeFormula LNT codeLNTFunction codeLNTRelation x) x0 (codeTerm (Succ (var x0)))))) (codeForall x0 (code.codeFormula LNT codeLNTFunction codeLNTRelation x))))) with (codeClose (code.codeFormula LNT codeLNTFunction codeLNTRelation (impH (substituteFormula LNT x x0 Zero) (impH (forallH x0 (impH x (substituteFormula LNT x x0 (Succ (var x0))))) (forallH x0 x))))).
rewrite <- beq_nat_refl.
reflexivity.
simpl in |- *.
unfold codeTerm in |- *.
repeat rewrite codeSubFormulaCorrect.
reflexivity.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
unfold close in |- *.
induction (ListExt.no_dup nat eq_nat_dec (freeVarFormula LNT (impH (substituteFormula LNT x x0 Zero) (impH (forallH x0 (impH x (substituteFormula LNT x x0 (Succ (var x0))))) (forallH x0 x))))).
reflexivity.
simpl in |- *.
assumption.

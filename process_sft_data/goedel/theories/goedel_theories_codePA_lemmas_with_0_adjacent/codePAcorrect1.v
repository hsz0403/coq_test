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

Lemma codePAcorrect1 : forall f : Formula, codePA (codeFormula f) = true -> mem Formula PA f.
Proof.
intros.
induction (PAdec f).
assumption.
unfold codePA in H.
unfold orRel, nat_rec, nat_rect in H.
unfold PA in |- *.
induction (eq_nat_dec (codeFormula PA6) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA6.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
clear b.
induction (eq_nat_dec (codeFormula PA5) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA5.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
clear b.
induction (eq_nat_dec (codeFormula PA4) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA4.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
clear b.
induction (eq_nat_dec (codeFormula PA3) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA3.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
clear b.
induction (eq_nat_dec (codeFormula PA2) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA2.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
clear b.
induction (eq_nat_dec (codeFormula PA1) (codeFormula f)).
rewrite a in H.
rewrite <- beq_nat_refl in H.
replace f with PA1.
right; constructor.
eapply codeFormulaInj.
apply a.
left.
rewrite beq_nat_not_refl in H.
apply codeInductionSchemaCorrect2.
simpl in H.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.

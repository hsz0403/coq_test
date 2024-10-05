Require Import primRec.
Require Import codeFreeVar.
Require Import codeSubFormula.
Require Import cPair.
Require Import Arith.
Require Import code.
Require Import folProp.
Require Import extEqualNat.
Require Import wellFormed.
Require Import folProof.
Require Import prLogic.
Section Check_Proof.
Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.
Variable codeArityF : nat -> nat.
Variable codeArityR : nat -> nat.
Hypothesis codeArityFIsPR : isPR 1 codeArityF.
Hypothesis codeArityFIsCorrect1 : forall f : Functions L, codeArityF (codeF f) = S (arity L (inr _ f)).
Hypothesis codeArityFIsCorrect2 : forall n : nat, codeArityF n <> 0 -> exists f : Functions L, codeF f = n.
Hypothesis codeArityRIsPR : isPR 1 codeArityR.
Hypothesis codeArityRIsCorrect1 : forall r : Relations L, codeArityR (codeR r) = S (arity L (inl _ r)).
Hypothesis codeArityRIsCorrect2 : forall n : nat, codeArityR n <> 0 -> exists r : Relations L, codeR r = n.
Hypothesis codeFInj : forall f g : Functions L, codeF f = codeF g -> f = g.
Hypothesis codeRInj : forall R S : Relations L, codeR R = codeR S -> R = S.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Let Formula := Formula L.
Let equal := equal L.
Let atomic := atomic L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Let wellFormedTerm := wellFormedTerm codeArityF.
Let wellFormedFormula := wellFormedFormula codeArityF codeArityR.
Let Prf := Prf L.
Definition checkPrfAXM (p recs : nat) := switchPR (charFunction 2 beq_nat (cPairPi2 (cPairPi2 p)) (cPairPi1 p)) (S (S (cPair (cPairPi1 p) 0))) 0.
Definition checkPrfMP (p recs : nat) := switchPR (wellFormedFormula (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) * (charFunction 2 beq_nat (cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 p)))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 p)) * (codeNth (p - S (cPairPi1 (cPairPi2 (cPairPi2 p)))) recs * codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs))) (S (codeApp (pred (codeNth (p - S (cPairPi1 (cPairPi2 (cPairPi2 p)))) recs)) (pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs)))) 0.
Definition checkPrfGEN (p recs : nat) := switchPR (charFunction 2 beq_nat (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (cPairPi1 p) * (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs * (1 - codeIn (cPairPi1 (cPairPi2 (cPairPi2 p))) (codeFreeVarListFormula (pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs)))))) (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs) 0.
Definition checkPrfIMP1 (p recs : nat) := let A := cPairPi1 (cPairPi2 (cPairPi2 p)) in let B := cPairPi2 (cPairPi2 (cPairPi2 p)) in charFunction 2 beq_nat (cPair 1 (cPair A (cPair 1 (cPair B A)))) (cPairPi1 p).
Definition checkPrfIMP2 (p recs : nat) := let A := cPairPi1 (cPairPi2 (cPairPi2 p)) in let B := cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))) in let C := cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))) in charFunction 2 beq_nat (cPair 1 (cPair (cPair 1 (cPair A (cPair 1 (cPair B C)))) (cPair 1 (cPair (cPair 1 (cPair A B)) (cPair 1 (cPair A C)))))) (cPairPi1 p).
Definition checkPrfCP (p recs : nat) := let A := cPairPi1 (cPairPi2 (cPairPi2 p)) in let B := cPairPi2 (cPairPi2 (cPairPi2 p)) in charFunction 2 beq_nat (cPair 1 (cPair (cPair 1 (cPair (cPair 2 A) (cPair 2 B))) (cPair 1 (cPair B A)))) (cPairPi1 p).
Definition checkPrfFA1 (p recs : nat) := let A := cPairPi1 (cPairPi2 (cPairPi2 p)) in let v := cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))) in let t := cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))) in wellFormedTerm t * charFunction 2 beq_nat (cPair 1 (cPair (cPair 3 (cPair v A)) (codeSubFormula A v t))) (cPairPi1 p).
Definition checkPrfFA2 (p recs : nat) := let A := cPairPi1 (cPairPi2 (cPairPi2 p)) in let v := cPairPi2 (cPairPi2 (cPairPi2 p)) in (1 - codeIn v (codeFreeVarFormula A)) * charFunction 2 beq_nat (cPair 1 (cPair A (cPair 3 (cPair v A)))) (cPairPi1 p).
Definition checkPrfFA3 (p recs : nat) := let A := cPairPi1 (cPairPi2 (cPairPi2 p)) in let B := cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))) in let v := cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))) in charFunction 2 beq_nat (cPair 1 (cPair (cPair 3 (cPair v (cPair 1 (cPair A B)))) (cPair 1 (cPair (cPair 3 (cPair v A)) (cPair 3 (cPair v B)))))) (cPairPi1 p).
Definition checkPrfEQ1 (p recs : nat) := charFunction 2 beq_nat (cPairPi2 (cPairPi2 p)) 0 * charFunction 2 beq_nat (codeFormula L codeF codeR (fol.equal L (fol.var L 0) (fol.var L 0))) (cPairPi1 p).
Definition checkPrfEQ2 (p recs : nat) := charFunction 2 beq_nat (cPairPi2 (cPairPi2 p)) 0 * charFunction 2 beq_nat (codeFormula L codeF codeR (fol.impH L (fol.equal L (fol.var L 0) (fol.var L 1)) (fol.equal L (fol.var L 1) (fol.var L 0)))) (cPairPi1 p).
Definition checkPrfEQ3 (p recs : nat) := charFunction 2 beq_nat (cPairPi2 (cPairPi2 p)) 0 * charFunction 2 beq_nat (codeFormula L codeF codeR (fol.impH L (fol.equal L (fol.var L 0) (fol.var L 1)) (fol.impH L (fol.equal L (fol.var L 1) (fol.var L 2)) (fol.equal L (fol.var L 0) (fol.var L 2))))) (cPairPi1 p).
Definition codeAxmEqHelp (n f : nat) : nat := nat_rec (fun _ => nat) f (fun m rec : nat => cPair 1 (cPair (cPair 0 (cPair (cPair 0 (m + m)) (cPair 0 (S (m + m))))) rec)) n.
Definition codeNVars1 (n : nat) : nat := nat_rec (fun _ => nat) 0 (fun m rec : nat => S (cPair (cPair 0 (m + m)) rec)) n.
Definition codeNVars2 (n : nat) : nat := nat_rec (fun _ => nat) 0 (fun m rec : nat => S (cPair (cPair 0 (S (m + m))) rec)) n.
Definition checkPrfEQ4 (p recs : nat) := let r := cPairPi2 (cPairPi2 p) in let A := cPair (S (S (S (S r)))) (codeNVars1 (pred (codeArityR r))) in let B := cPair (S (S (S (S r)))) (codeNVars2 (pred (codeArityR r))) in notZero (codeArityR r) * charFunction 2 beq_nat (codeAxmEqHelp (pred (codeArityR r)) (codeIff A B)) (cPairPi1 p).
Definition checkPrfEQ5 (p recs : nat) := let f := cPairPi2 (cPairPi2 p) in notZero (codeArityF f) * charFunction 2 beq_nat (codeAxmEqHelp (pred (codeArityF f)) (cPair 0 (cPair (cPair (S f) (codeNVars1 (pred (codeArityF f)))) (cPair (S f) (codeNVars2 (pred (codeArityF f))))))) (cPairPi1 p).
Definition checkPrfHelp : nat -> nat := evalStrongRec 0 (fun p recs : nat => let type := cPairPi1 (cPairPi2 p) in switchPR type (switchPR (pred type) (switchPR (pred (pred type)) (switchPR (pred (pred (pred type))) (switchPR (pred (pred (pred (pred type)))) (switchPR (pred (pred (pred (pred (pred type))))) (switchPR (pred (pred (pred (pred (pred (pred type)))))) (switchPR (pred (pred (pred (pred (pred (pred (pred type))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred type)))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred type))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred type)))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred type))))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred type)))))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred type))))))))))))) 0 (checkPrfEQ5 p recs)) (checkPrfEQ4 p recs)) (checkPrfEQ3 p recs)) (checkPrfEQ2 p recs)) (checkPrfEQ1 p recs)) (checkPrfFA3 p recs)) (checkPrfFA2 p recs)) (checkPrfFA1 p recs)) (checkPrfCP p recs)) (checkPrfIMP2 p recs)) (checkPrfIMP1 p recs)) (checkPrfGEN p recs)) (checkPrfMP p recs)) (checkPrfAXM p recs)).
Definition checkPrf (f p : nat) : nat := switchPR (wellFormedFormula f) (checkPrfHelp (cPair f p)) 0.
End Check_Proof.

Lemma checkPrfAXMIsPR : isPR 2 checkPrfAXM.
Proof.
unfold checkPrfAXM in |- *.
apply filter10IsPR with (g := fun p : nat => switchPR (charFunction 2 beq_nat (cPairPi2 (cPairPi2 p)) (cPairPi1 p)) (S (S (cPair (cPairPi1 p) 0))) 0).
apply compose1_3IsPR with (f1 := fun p : nat => charFunction 2 beq_nat (cPairPi2 (cPairPi2 p)) (cPairPi1 p)) (f2 := fun p : nat => S (S (cPair (cPairPi1 p) 0))) (f3 := fun p : nat => 0).
apply compose1_2IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply eqIsPR.
apply compose1_1IsPR with (f := fun p : nat => S (cPair (cPairPi1 p) 0)).
apply compose1_1IsPR with (f := fun p : nat => cPair (cPairPi1 p) 0).
apply compose1_2IsPR with (f' := fun p : nat => 0).
apply cPairPi1IsPR.
apply const1_NIsPR.
apply cPairIsPR.
apply succIsPR.
apply succIsPR.
apply const1_NIsPR.
Admitted.

Lemma checkPrfGENIsPR : isPR 2 checkPrfGEN.
Proof.
unfold checkPrfGEN in |- *.
apply compose2_3IsPR with (f1 := fun p recs : nat => charFunction 2 beq_nat (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (cPairPi1 p) * (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs * (1 - codeIn (cPairPi1 (cPairPi2 (cPairPi2 p))) (codeFreeVarListFormula (pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs)))))) (f2 := fun p recs : nat => codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs) (f3 := fun p recs : nat => 0).
apply compose2_2IsPR with (f := fun p recs : nat => charFunction 2 beq_nat (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (cPairPi1 p)) (g := fun p recs : nat => codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs * (1 - codeIn (cPairPi1 (cPairPi2 (cPairPi2 p))) (codeFreeVarListFormula (pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs))))).
apply filter10IsPR with (g := fun p : nat => charFunction 2 beq_nat (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (cPairPi1 p)).
apply compose1_2IsPR with (f := fun p : nat => cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (f' := fun p : nat => cPairPi1 p).
apply compose1_2IsPR with (f := fun p : nat => 3) (f' := fun p : nat => cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
apply const1_NIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply cPairIsPR.
apply cPairIsPR.
apply cPairPi1IsPR.
apply eqIsPR.
apply compose2_2IsPR with (f := fun p recs : nat => codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs) (g := fun p recs : nat => 1 - codeIn (cPairPi1 (cPairPi2 (cPairPi2 p))) (codeFreeVarListFormula (pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs)))).
apply callIsPR with (g := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply compose2_2IsPR with (f := fun p recs : nat => 1) (g := fun p recs : nat => codeIn (cPairPi1 (cPairPi2 (cPairPi2 p))) (codeFreeVarListFormula (pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs)))).
apply filter10IsPR with (g := fun _ : nat => 1).
apply const1_NIsPR.
apply compose2_2IsPR with (f := fun p recs : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (g := fun p recs : nat => codeFreeVarListFormula (pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs))).
apply filter10IsPR with (g := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply compose2_1IsPR with (f := fun p recs : nat => pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs)).
apply compose2_1IsPR with (f := fun p recs : nat => codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs).
apply callIsPR with (g := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply predIsPR.
apply codeFreeVarListFormulaIsPR.
apply codeInIsPR.
apply minusIsPR.
apply multIsPR.
apply multIsPR.
apply callIsPR with (g := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
Admitted.

Lemma checkPrfIMP1IsPR : isPR 2 checkPrfIMP1.
Proof.
unfold checkPrfIMP1 in |- *.
apply filter10IsPR with (g := fun p : nat => charFunction 2 beq_nat (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 1 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))))) (cPairPi1 p)).
assert (isPR 1 (fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
assert (isPR 1 (fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply compose1_2IsPR with (f := fun p : nat => cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 1 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))))).
apply compose1_2IsPR with (f := fun p : nat => 1) (f' := fun p : nat => cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 1 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p)))))).
apply const1_NIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => cPair 1 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))).
assumption.
apply compose1_2IsPR with (f := fun p : nat => 1) (f' := fun p : nat => cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p)))).
apply const1_NIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))).
assumption.
assumption.
apply cPairIsPR.
apply cPairIsPR.
apply cPairIsPR.
apply cPairIsPR.
apply cPairPi1IsPR.
Admitted.

Lemma checkPrfIMP2IsPR : isPR 2 checkPrfIMP2.
Proof.
unfold checkPrfIMP2 in |- *.
apply filter10IsPR with (g := fun p : nat => charFunction 2 beq_nat (cPair 1 (cPair (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))) (cPair 1 (cPair (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))))) (cPairPi1 p)).
assert (isPR 1 (fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
assert (isPR 1 (fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
assert (isPR 1 (fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply compose1_2IsPR with (f := fun p : nat => cPair 1 (cPair (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))) (cPair 1 (cPair (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))))).
replace (fun p : nat => cPair 1 (cPair (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))) (cPair 1 (cPair (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))))) with (fun p : nat => codeImp (codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (codeImp (codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))))); [ idtac | reflexivity ].
apply compose1_2IsPR with (f := fun p : nat => codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (f' := fun p : nat => codeImp (codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))).
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
assumption.
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))).
assumption.
assumption.
apply codeImpIsPR.
apply codeImpIsPR.
apply compose1_2IsPR with (f := fun p : nat => codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))) (f' := fun p : nat => codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))).
assumption.
assumption.
apply codeImpIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))).
assumption.
assumption.
apply codeImpIsPR.
apply codeImpIsPR.
apply codeImpIsPR.
apply cPairPi1IsPR.
Admitted.

Lemma checkPrfCPIsPR : isPR 2 checkPrfCP.
Proof.
unfold checkPrfCP in |- *.
apply filter10IsPR with (g := fun p : nat => charFunction 2 beq_nat (cPair 1 (cPair (cPair 1 (cPair (cPair 2 (cPairPi1 (cPairPi2 (cPairPi2 p)))) (cPair 2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (cPair 1 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))))) (cPairPi1 p)).
assert (isPR 1 (fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
assert (isPR 1 (fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply compose1_2IsPR with (f := fun p : nat => cPair 1 (cPair (cPair 1 (cPair (cPair 2 (cPairPi1 (cPairPi2 (cPairPi2 p)))) (cPair 2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (cPair 1 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))))).
replace (fun p : nat => cPair 1 (cPair (cPair 1 (cPair (cPair 2 (cPairPi1 (cPairPi2 (cPairPi2 p)))) (cPair 2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))) (cPair 1 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))))) with (fun p : nat => codeImp (codeImp (codeNot (cPairPi1 (cPairPi2 (cPairPi2 p)))) (codeNot (cPairPi2 (cPairPi2 (cPairPi2 p))))) (codeImp (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))); [ idtac | reflexivity ].
apply compose1_2IsPR with (f := fun p : nat => codeImp (codeNot (cPairPi1 (cPairPi2 (cPairPi2 p)))) (codeNot (cPairPi2 (cPairPi2 (cPairPi2 p))))) (f' := fun p : nat => codeImp (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p)))).
apply compose1_2IsPR with (f := fun p : nat => codeNot (cPairPi1 (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => codeNot (cPairPi2 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))).
assumption.
apply codeNotIsPR.
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
assumption.
apply codeNotIsPR.
apply codeImpIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))).
assumption.
assumption.
apply codeImpIsPR.
apply codeImpIsPR.
apply cPairPi1IsPR.
Admitted.

Lemma checkPrfFA1IsPR : isPR 2 checkPrfFA1.
Proof.
unfold checkPrfFA1 in |- *.
apply filter10IsPR with (g := fun p : nat => wellFormedTerm (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) * charFunction 2 beq_nat (cPair 1 (cPair (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (codeSubFormula (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))))) (cPairPi1 p)).
assert (isPR 1 (fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
assert (isPR 1 (fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
assert (isPR 1 (fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply compose1_2IsPR with (f := fun p : nat => wellFormedTerm (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))) (f' := fun p : nat => charFunction 2 beq_nat (cPair 1 (cPair (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (codeSubFormula (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))))) (cPairPi1 p)).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))).
assumption.
unfold wellFormedTerm in |- *.
apply wellFormedTermIsPR.
apply codeArityFIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPair 1 (cPair (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (codeSubFormula (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))))).
replace (fun p : nat => cPair 1 (cPair (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (codeSubFormula (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))))) with (fun p : nat => codeImp (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (codeSubFormula (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))))); [ idtac | reflexivity ].
apply compose1_2IsPR with (f := fun p : nat => cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (f' := fun p : nat => codeSubFormula (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (g := fun a b : nat => cPair 3 (cPair a b)).
assumption.
assumption.
apply codeForallIsPR.
apply compose1_3IsPR with (f1 := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (f2 := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (f3 := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))); try assumption.
apply codeSubFormulaIsPR.
apply codeImpIsPR.
apply cPairPi1IsPR.
apply eqIsPR.
Admitted.

Lemma checkPrfFA2IsPR : isPR 2 checkPrfFA2.
Proof.
unfold checkPrfFA2 in |- *.
apply filter10IsPR with (g := fun p : nat => (1 - codeIn (cPairPi2 (cPairPi2 (cPairPi2 p))) (codeFreeVarFormula (cPairPi1 (cPairPi2 (cPairPi2 p))))) * charFunction 2 beq_nat (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))))) (cPairPi1 p)).
assert (isPR 1 (fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
assert (isPR 1 (fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply compose1_2IsPR with (f := fun p : nat => 1 - codeIn (cPairPi2 (cPairPi2 (cPairPi2 p))) (codeFreeVarFormula (cPairPi1 (cPairPi2 (cPairPi2 p))))) (f' := fun p : nat => charFunction 2 beq_nat (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))))) (cPairPi1 p)).
apply compose1_2IsPR with (f := fun p : nat => 1) (f' := fun p : nat => codeIn (cPairPi2 (cPairPi2 (cPairPi2 p))) (codeFreeVarFormula (cPairPi1 (cPairPi2 (cPairPi2 p))))).
apply const1_NIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => codeFreeVarFormula (cPairPi1 (cPairPi2 (cPairPi2 p)))).
assumption.
apply compose1_1IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))).
assumption.
apply codeFreeVarFormulaIsPR.
apply codeInIsPR.
apply minusIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))))).
replace (fun p : nat => cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))))) with (fun p : nat => codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p)))))); [ idtac | reflexivity ].
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 p))))).
assumption.
apply compose1_2IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (g := fun a b : nat => cPair 3 (cPair a b)).
assumption.
assumption.
apply codeForallIsPR.
apply codeImpIsPR.
apply cPairPi1IsPR.
apply eqIsPR.
Admitted.

Lemma checkPrfFA3IsPR : isPR 2 checkPrfFA3.
Proof.
unfold checkPrfFA3 in |- *.
apply filter10IsPR with (g := fun p : nat => charFunction 2 beq_nat (cPair 1 (cPair (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))) (cPair 1 (cPair (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))))) (cPairPi1 p)).
assert (isPR 1 (fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
assert (isPR 1 (fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
assert (isPR 1 (fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply compose1_2IsPR with (f := fun p : nat => cPair 1 (cPair (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))) (cPair 1 (cPair (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))))).
replace (fun p : nat => cPair 1 (cPair (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))) (cPair 1 (cPair (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))))) with (fun p : nat => codeImp (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))))) (codeImp (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))))); [ idtac | reflexivity ].
apply compose1_2IsPR with (f := fun p : nat => cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))))) (f' := fun p : nat => codeImp (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))))).
apply compose1_2IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => codeImp (cPairPi1 (cPairPi2 (cPairPi2 p))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))) (g := fun a b : nat => cPair 3 (cPair a b)).
assumption.
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))).
assumption.
assumption.
apply codeImpIsPR.
apply codeForallIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 p))))) (f' := fun p : nat => cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))))).
apply compose1_2IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))) (g := fun a b : nat => cPair 3 (cPair a b)).
assumption.
assumption.
apply codeForallIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (g := fun a b : nat => cPair 3 (cPair a b)).
assumption.
assumption.
apply codeForallIsPR.
apply codeImpIsPR.
apply codeImpIsPR.
apply cPairPi1IsPR.
Admitted.

Lemma checkPrfEQnIsPR : forall n : nat, isPR 2 (fun p recs : nat => charFunction 2 beq_nat (cPairPi2 (cPairPi2 p)) 0 * charFunction 2 beq_nat n (cPairPi1 p)).
Proof.
unfold checkPrfEQ1 in |- *.
intros.
apply filter10IsPR with (g := fun p : nat => charFunction 2 beq_nat (cPairPi2 (cPairPi2 p)) 0 * charFunction 2 beq_nat n (cPairPi1 p)).
apply compose1_2IsPR with (f := fun p : nat => charFunction 2 beq_nat (cPairPi2 (cPairPi2 p)) 0) (f' := fun p : nat => charFunction 2 beq_nat n (cPairPi1 p)).
apply compose1_2IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)) (f' := fun p : nat => 0).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply const1_NIsPR.
apply eqIsPR.
apply compose1_2IsPR with (f := fun p : nat => n).
apply const1_NIsPR.
apply cPairPi1IsPR.
apply eqIsPR.
Admitted.

Lemma checkPrfEQ1IsPR : isPR 2 checkPrfEQ1.
Proof.
unfold checkPrfEQ1 in |- *.
Admitted.

Lemma checkPrfEQ2IsPR : isPR 2 checkPrfEQ2.
Proof.
unfold checkPrfEQ2 in |- *.
Admitted.

Lemma checkPrfEQ3IsPR : isPR 2 checkPrfEQ3.
Proof.
unfold checkPrfEQ3 in |- *.
Admitted.

Lemma codeAxmEqHelpIsPR : isPR 2 codeAxmEqHelp.
Proof.
unfold codeAxmEqHelp in |- *.
apply ind1ParamIsPR with (g := fun f : nat => f) (f := fun m rec f : nat => cPair 1 (cPair (cPair 0 (cPair (cPair 0 (m + m)) (cPair 0 (S (m + m))))) rec)).
apply filter110IsPR with (g := fun m rec : nat => codeImp (cPair 0 (cPair (cPair 0 (m + m)) (cPair 0 (S (m + m))))) rec).
apply compose2_2IsPR with (f := fun m rec : nat => cPair 0 (cPair (cPair 0 (m + m)) (cPair 0 (S (m + m))))) (g := fun m rec : nat => rec).
apply filter10IsPR with (g := fun m : nat => cPair 0 (cPair (cPair 0 (m + m)) (cPair 0 (S (m + m))))).
assert (forall g : nat -> nat, isPR 1 g -> isPR 1 (fun a : nat => cPair 0 (g a))).
intros.
apply compose1_2IsPR with (f := fun a : nat => 0).
apply const1_NIsPR.
assumption.
apply cPairIsPR.
apply H with (g := fun m : nat => cPair (cPair 0 (m + m)) (cPair 0 (S (m + m)))).
apply compose1_2IsPR with (f := fun m : nat => cPair 0 (m + m)) (f' := fun m : nat => cPair 0 (S (m + m))).
apply H with (g := fun m : nat => m + m).
apply compose1_2IsPR with (f := fun m : nat => m) (f' := fun m : nat => m).
apply idIsPR.
apply idIsPR.
apply plusIsPR.
apply H with (g := fun m : nat => S (m + m)).
apply compose1_1IsPR with (f := fun m : nat => m + m).
apply compose1_2IsPR with (f := fun m : nat => m) (f' := fun m : nat => m).
apply idIsPR.
apply idIsPR.
apply plusIsPR.
apply succIsPR.
apply cPairIsPR.
apply pi2_2IsPR.
apply codeImpIsPR.
Admitted.

Lemma codeNVars1IsPR : isPR 1 codeNVars1.
Proof.
unfold codeNVars1 in |- *.
apply indIsPR with (f := fun m rec : nat => S (cPair (cPair 0 (m + m)) rec)).
apply compose2_1IsPR with (f := fun m rec : nat => cPair (cPair 0 (m + m)) rec).
apply compose2_2IsPR with (f := fun m rec : nat => cPair 0 (m + m)) (g := fun m rec : nat => rec).
apply filter10IsPR with (g := fun m : nat => cPair 0 (m + m)).
apply compose1_2IsPR with (f := fun m : nat => 0) (f' := fun m : nat => m + m).
apply const1_NIsPR.
apply compose1_2IsPR with (f := fun m : nat => m) (f' := fun m : nat => m).
apply idIsPR.
apply idIsPR.
apply plusIsPR.
apply cPairIsPR.
apply pi2_2IsPR.
apply cPairIsPR.
Admitted.

Lemma codeNVars2IsPR : isPR 1 codeNVars2.
Proof.
unfold codeNVars2 in |- *.
apply indIsPR with (f := fun m rec : nat => S (cPair (cPair 0 (S (m + m))) rec)).
apply compose2_1IsPR with (f := fun m rec : nat => cPair (cPair 0 (S (m + m))) rec).
apply compose2_2IsPR with (f := fun m rec : nat => cPair 0 (S (m + m))) (g := fun m rec : nat => rec).
apply filter10IsPR with (g := fun m : nat => cPair 0 (S (m + m))).
apply compose1_2IsPR with (f := fun m : nat => 0) (f' := fun m : nat => S (m + m)).
apply const1_NIsPR.
apply compose1_1IsPR with (f := fun m : nat => m + m).
apply compose1_2IsPR with (f := fun m : nat => m) (f' := fun m : nat => m).
apply idIsPR.
apply idIsPR.
apply plusIsPR.
apply succIsPR.
apply cPairIsPR.
apply pi2_2IsPR.
apply cPairIsPR.
Admitted.

Lemma codeNVarsCorrect : forall n : nat, codeNVars1 n = codeTerms L codeF n (fst (nVars L n)) /\ codeNVars2 n = codeTerms L codeF n (snd (nVars L n)).
Proof.
intros.
split.
induction n as [| n Hrecn].
simpl in |- *.
reflexivity.
simpl in |- *.
rewrite Hrecn.
induction (nVars L n).
simpl in |- *.
reflexivity.
induction n as [| n Hrecn].
simpl in |- *.
reflexivity.
simpl in |- *.
rewrite Hrecn.
induction (nVars L n).
simpl in |- *.
Admitted.

Lemma codeOrIsPR : isPR 2 codeOr.
Proof.
unfold codeOr in |- *.
apply compose2_2IsPR with (f := fun a b : nat => codeNot a) (g := fun a b : nat => b).
apply filter10IsPR.
apply codeNotIsPR.
apply pi2_2IsPR.
Admitted.

Lemma codeAndIsPR : isPR 2 codeAnd.
Proof.
unfold codeAnd in |- *.
apply compose2_1IsPR with (f := fun a b : nat => codeOr (codeNot a) (codeNot b)).
apply compose2_2IsPR with (f := fun a b : nat => codeNot a) (g := fun a b : nat => codeNot b).
apply filter10IsPR.
apply codeNotIsPR.
apply filter01IsPR.
apply codeNotIsPR.
apply codeOrIsPR.
Admitted.

Lemma codeIffIsPR : isPR 2 codeIff.
Proof.
unfold codeIff in |- *.
apply compose2_2IsPR with (g := fun a b : nat => codeImp b a).
apply codeImpIsPR.
apply swapIsPR.
apply codeImpIsPR.
Admitted.

Lemma checkPrfEQ4IsPR : isPR 2 checkPrfEQ4.
Proof.
unfold checkPrfEQ4 in |- *.
apply filter10IsPR with (g := fun p : nat => notZero (codeArityR (cPairPi2 (cPairPi2 p))) * charFunction 2 beq_nat (codeAxmEqHelp (pred (codeArityR (cPairPi2 (cPairPi2 p)))) (codeIff (cPair (S (S (S (S (cPairPi2 (cPairPi2 p)))))) (codeNVars1 (pred (codeArityR (cPairPi2 (cPairPi2 p)))))) (cPair (S (S (S (S (cPairPi2 (cPairPi2 p)))))) (codeNVars2 (pred (codeArityR (cPairPi2 (cPairPi2 p)))))))) (cPairPi1 p)).
assert (isPR 1 (fun p : nat => cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply compose1_2IsPR with (f := fun p : nat => notZero (codeArityR (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => charFunction 2 beq_nat (codeAxmEqHelp (pred (codeArityR (cPairPi2 (cPairPi2 p)))) (codeIff (cPair (S (S (S (S (cPairPi2 (cPairPi2 p)))))) (codeNVars1 (pred (codeArityR (cPairPi2 (cPairPi2 p)))))) (cPair (S (S (S (S (cPairPi2 (cPairPi2 p)))))) (codeNVars2 (pred (codeArityR (cPairPi2 (cPairPi2 p)))))))) (cPairPi1 p)).
apply compose1_1IsPR with (f := fun p : nat => codeArityR (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
assumption.
apply codeArityRIsPR.
apply notZeroIsPR.
apply compose1_2IsPR with (f := fun p : nat => codeAxmEqHelp (pred (codeArityR (cPairPi2 (cPairPi2 p)))) (codeIff (cPair (S (S (S (S (cPairPi2 (cPairPi2 p)))))) (codeNVars1 (pred (codeArityR (cPairPi2 (cPairPi2 p)))))) (cPair (S (S (S (S (cPairPi2 (cPairPi2 p)))))) (codeNVars2 (pred (codeArityR (cPairPi2 (cPairPi2 p)))))))).
apply compose1_2IsPR with (f := fun p : nat => pred (codeArityR (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => codeIff (cPair (S (S (S (S (cPairPi2 (cPairPi2 p)))))) (codeNVars1 (pred (codeArityR (cPairPi2 (cPairPi2 p)))))) (cPair (S (S (S (S (cPairPi2 (cPairPi2 p)))))) (codeNVars2 (pred (codeArityR (cPairPi2 (cPairPi2 p))))))).
apply compose1_1IsPR with (f := fun p : nat => codeArityR (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
assumption.
apply codeArityRIsPR.
apply predIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPair (S (S (S (S (cPairPi2 (cPairPi2 p)))))) (codeNVars1 (pred (codeArityR (cPairPi2 (cPairPi2 p)))))) (f' := fun p : nat => cPair (S (S (S (S (cPairPi2 (cPairPi2 p)))))) (codeNVars2 (pred (codeArityR (cPairPi2 (cPairPi2 p)))))).
apply compose1_2IsPR with (f := fun p : nat => S (S (S (S (cPairPi2 (cPairPi2 p)))))) (f' := fun p : nat => codeNVars1 (pred (codeArityR (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)) (g := iterate S 4).
assumption.
apply iterateIsPR.
apply succIsPR.
apply compose1_1IsPR with (f := fun p : nat => pred (codeArityR (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => codeArityR (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
assumption.
apply codeArityRIsPR.
apply predIsPR.
apply codeNVars1IsPR.
apply cPairIsPR.
apply compose1_2IsPR with (f := fun p : nat => S (S (S (S (cPairPi2 (cPairPi2 p)))))) (f' := fun p : nat => codeNVars2 (pred (codeArityR (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)) (g := iterate S 4).
assumption.
apply iterateIsPR.
apply succIsPR.
apply compose1_1IsPR with (f := fun p : nat => pred (codeArityR (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => codeArityR (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
assumption.
apply codeArityRIsPR.
apply predIsPR.
apply codeNVars2IsPR.
apply cPairIsPR.
apply codeIffIsPR.
apply codeAxmEqHelpIsPR.
apply cPairPi1IsPR.
apply eqIsPR.
Admitted.

Lemma checkPrfEQ5IsPR : isPR 2 checkPrfEQ5.
Proof.
unfold checkPrfEQ5 in |- *.
apply filter10IsPR with (g := fun p : nat => notZero (codeArityF (cPairPi2 (cPairPi2 p))) * charFunction 2 beq_nat (codeAxmEqHelp (pred (codeArityF (cPairPi2 (cPairPi2 p)))) (cPair 0 (cPair (cPair (S (cPairPi2 (cPairPi2 p))) (codeNVars1 (pred (codeArityF (cPairPi2 (cPairPi2 p)))))) (cPair (S (cPairPi2 (cPairPi2 p))) (codeNVars2 (pred (codeArityF (cPairPi2 (cPairPi2 p))))))))) (cPairPi1 p)).
assert (isPR 1 (fun p : nat => cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply compose1_2IsPR with (f := fun p : nat => notZero (codeArityF (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => charFunction 2 beq_nat (codeAxmEqHelp (pred (codeArityF (cPairPi2 (cPairPi2 p)))) (cPair 0 (cPair (cPair (S (cPairPi2 (cPairPi2 p))) (codeNVars1 (pred (codeArityF (cPairPi2 (cPairPi2 p)))))) (cPair (S (cPairPi2 (cPairPi2 p))) (codeNVars2 (pred (codeArityF (cPairPi2 (cPairPi2 p))))))))) (cPairPi1 p)).
apply compose1_1IsPR with (f := fun p : nat => codeArityF (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
assumption.
apply codeArityFIsPR.
apply notZeroIsPR.
apply compose1_2IsPR with (f := fun p : nat => codeAxmEqHelp (pred (codeArityF (cPairPi2 (cPairPi2 p)))) (cPair 0 (cPair (cPair (S (cPairPi2 (cPairPi2 p))) (codeNVars1 (pred (codeArityF (cPairPi2 (cPairPi2 p)))))) (cPair (S (cPairPi2 (cPairPi2 p))) (codeNVars2 (pred (codeArityF (cPairPi2 (cPairPi2 p))))))))).
apply compose1_2IsPR with (f := fun p : nat => pred (codeArityF (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => cPair 0 (cPair (cPair (S (cPairPi2 (cPairPi2 p))) (codeNVars1 (pred (codeArityF (cPairPi2 (cPairPi2 p)))))) (cPair (S (cPairPi2 (cPairPi2 p))) (codeNVars2 (pred (codeArityF (cPairPi2 (cPairPi2 p)))))))).
apply compose1_1IsPR with (f := fun p : nat => codeArityF (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
assumption.
apply codeArityFIsPR.
apply predIsPR.
apply compose1_2IsPR with (f := fun p : nat => cPair (S (cPairPi2 (cPairPi2 p))) (codeNVars1 (pred (codeArityF (cPairPi2 (cPairPi2 p)))))) (f' := fun p : nat => cPair (S (cPairPi2 (cPairPi2 p))) (codeNVars2 (pred (codeArityF (cPairPi2 (cPairPi2 p)))))) (g := fun a b : nat => cPair 0 (cPair a b)).
apply compose1_2IsPR with (f := fun p : nat => S (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => codeNVars1 (pred (codeArityF (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
assumption.
apply succIsPR.
apply compose1_1IsPR with (f := fun p : nat => pred (codeArityF (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => codeArityF (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
assumption.
apply codeArityFIsPR.
apply predIsPR.
apply codeNVars1IsPR.
apply cPairIsPR.
apply compose1_2IsPR with (f := fun p : nat => S (cPairPi2 (cPairPi2 p))) (f' := fun p : nat => codeNVars2 (pred (codeArityF (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
assumption.
apply succIsPR.
apply compose1_1IsPR with (f := fun p : nat => pred (codeArityF (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => codeArityF (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
assumption.
apply codeArityFIsPR.
apply predIsPR.
apply codeNVars2IsPR.
apply cPairIsPR.
apply compose2_2IsPR with (f := fun a b : nat => 0).
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply cPairIsPR.
apply cPairIsPR.
apply codeAxmEqHelpIsPR.
apply cPairPi1IsPR.
apply eqIsPR.
Admitted.

Lemma checkPrfMPIsPR : isPR 2 checkPrfMP.
Proof.
unfold checkPrfMP in |- *.
apply compose2_3IsPR with (f1 := fun p recs : nat => wellFormedFormula (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) * (charFunction 2 beq_nat (cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 p)))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 p)) * (codeNth (p - S (cPairPi1 (cPairPi2 (cPairPi2 p)))) recs * codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs))) (f2 := fun p recs : nat => S (codeApp (pred (codeNth (p - S (cPairPi1 (cPairPi2 (cPairPi2 p)))) recs)) (pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs)))) (f3 := fun p recs : nat => 0).
apply compose2_2IsPR with (f := fun p recs : nat => wellFormedFormula (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))) (g := fun p recs : nat => charFunction 2 beq_nat (cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 p)))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 p)) * (codeNth (p - S (cPairPi1 (cPairPi2 (cPairPi2 p)))) recs * codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs)).
apply filter10IsPR with (g := fun p : nat => wellFormedFormula (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p))))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
unfold wellFormedFormula in |- *.
apply wellFormedFormulaIsPR.
apply codeArityFIsPR.
apply codeArityRIsPR.
apply compose2_2IsPR with (f := fun p recs : nat => charFunction 2 beq_nat (cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 p)))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 p))) (g := fun p recs : nat => codeNth (p - S (cPairPi1 (cPairPi2 (cPairPi2 p)))) recs * codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs).
apply filter10IsPR with (g := fun p : nat => charFunction 2 beq_nat (cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 p)))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 p))).
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 p)))) (f' := fun p : nat => codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))) (cPairPi1 p)).
apply compose1_1IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply cPairPi1IsPR.
apply compose1_2IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 p)))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply cPairPi1IsPR.
apply codeImpIsPR.
apply eqIsPR.
apply compose2_2IsPR with (f := fun p recs : nat => codeNth (p - S (cPairPi1 (cPairPi2 (cPairPi2 p)))) recs) (g := fun p recs : nat => codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs).
apply callIsPR with (g := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply callIsPR with (g := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply multIsPR.
apply multIsPR.
apply multIsPR.
apply compose2_1IsPR with (f := fun p recs : nat => codeApp (pred (codeNth (p - S (cPairPi1 (cPairPi2 (cPairPi2 p)))) recs)) (pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs))).
apply compose2_2IsPR with (f := fun p recs : nat => pred (codeNth (p - S (cPairPi1 (cPairPi2 (cPairPi2 p)))) recs)) (g := fun p recs : nat => pred (codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs)).
apply compose2_1IsPR with (f := fun p recs : nat => codeNth (p - S (cPairPi1 (cPairPi2 (cPairPi2 p)))) recs).
apply callIsPR with (g := fun p : nat => cPairPi1 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply predIsPR.
apply compose2_1IsPR with (f := fun p recs : nat => codeNth (p - S (cPairPi2 (cPairPi2 (cPairPi2 p)))) recs).
apply callIsPR with (g := fun p : nat => cPairPi2 (cPairPi2 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi2 (cPairPi2 p)).
apply compose1_1IsPR; apply cPairPi2IsPR.
apply cPairPi2IsPR.
apply predIsPR.
apply codeAppIsPR.
apply succIsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply switchIsPR.

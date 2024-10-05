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

Lemma checkPrfHelpIsPR : isPR 1 checkPrfHelp.
set (f := list_rec (fun _ => nat -> nat -> nat -> nat) (fun _ _ _ : nat => 0) (fun (a : nat -> nat -> nat) (l : list (nat -> nat -> nat)) (rec : nat -> nat -> nat -> nat) (n p recs : nat) => switchPR (iterate pred n (cPairPi1 (cPairPi2 p))) (rec (S n) p recs) (a p recs))) in *.
set (l := checkPrfAXM :: checkPrfMP :: checkPrfGEN :: checkPrfIMP1 :: checkPrfIMP2 :: checkPrfCP :: checkPrfFA1 :: checkPrfFA2 :: checkPrfFA3 :: checkPrfEQ1 :: checkPrfEQ2 :: checkPrfEQ3 :: checkPrfEQ4 :: checkPrfEQ5 :: nil) in *.
assert (forall (l : list (nat -> nat -> nat)) (n : nat), list_rect (fun _ => Set) unit (fun (a : nat -> nat -> nat) _ (rec : Set) => (isPR 2 a * rec)%type) l -> isPR 2 (f l n)).
intro.
induction l0 as [| a l0 Hrecl0].
simpl in |- *.
intros.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
simpl in |- *.
intros.
apply compose2_3IsPR with (f1 := fun p recs : nat => iterate pred n (cPairPi1 (cPairPi2 p))).
apply filter10IsPR with (g := fun p : nat => iterate pred n (cPairPi1 (cPairPi2 p))).
apply compose1_1IsPR with (f := fun p : nat => cPairPi1 (cPairPi2 p)).
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply cPairPi1IsPR.
apply iterateIsPR.
apply predIsPR.
apply Hrecl0.
eapply snd.
apply H.
eapply fst.
apply H.
apply switchIsPR.
assert (isPR 2 (f l 0)).
apply H.
simpl in |- *.
repeat split.
apply checkPrfAXMIsPR.
apply checkPrfMPIsPR.
apply checkPrfGENIsPR.
apply checkPrfIMP1IsPR.
apply checkPrfIMP2IsPR.
apply checkPrfCPIsPR.
apply checkPrfFA1IsPR.
apply checkPrfFA2IsPR.
apply checkPrfFA3IsPR.
apply checkPrfEQ1IsPR.
apply checkPrfEQ2IsPR.
apply checkPrfEQ3IsPR.
apply checkPrfEQ4IsPR.
apply checkPrfEQ5IsPR.
unfold checkPrfHelp in |- *.
apply evalStrongRecIsPR.
Admitted.

Lemma checkPrfIsPR : isPR 2 checkPrf.
Proof.
unfold checkPrf in |- *.
apply compose2_3IsPR with (f1 := fun f p : nat => wellFormedFormula f) (f2 := fun f p : nat => checkPrfHelp (cPair f p)) (f3 := fun f p : nat => 0).
apply filter10IsPR.
unfold wellFormedFormula in |- *.
apply wellFormedFormulaIsPR.
apply codeArityFIsPR.
apply codeArityRIsPR.
apply compose2_1IsPR.
apply cPairIsPR.
apply checkPrfHelpIsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
Admitted.

Lemma checkPrfCorrect1 : forall (l : list Formula) (f : Formula) (p : Prf l f), checkPrf (codeFormula L codeF codeR f) (codePrf L codeF codeR l f p) = S (codeList (map (codeFormula L codeF codeR) l)).
Proof.
intros.
unfold checkPrf in |- *.
rewrite (wellFormedFormulaCorrect1 L codeF codeArityF codeArityFIsCorrect1 codeR codeArityR codeArityRIsCorrect1).
simpl in |- *.
lazy beta delta [checkPrfHelp] in |- *.
set (A := fun p0 recs : nat => let type := cPairPi1 (cPairPi2 p0) in switchPR type (switchPR (pred type) (switchPR (pred (pred type)) (switchPR (pred (pred (pred type))) (switchPR (pred (pred (pred (pred type)))) (switchPR (pred (pred (pred (pred (pred type))))) (switchPR (pred (pred (pred (pred (pred (pred type)))))) (switchPR (pred (pred (pred (pred (pred (pred (pred type))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred type)))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred type))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred type)))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred type))))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred type)))))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred type))))))))))))) 0 (checkPrfEQ5 p0 recs)) (checkPrfEQ4 p0 recs)) (checkPrfEQ3 p0 recs)) (checkPrfEQ2 p0 recs)) (checkPrfEQ1 p0 recs)) (checkPrfFA3 p0 recs)) (checkPrfFA2 p0 recs)) (checkPrfFA1 p0 recs)) (checkPrfCP p0 recs)) (checkPrfIMP2 p0 recs)) (checkPrfIMP1 p0 recs)) (checkPrfGEN p0 recs)) (checkPrfMP p0 recs)) (checkPrfAXM p0 recs)) in *.
induction p as [A0| Axm1 Axm2 A0 B p1 Hrecp1 p0 Hrecp0| Axm A0 v n p Hrecp| A0 B| A0 B C| A0 B| A0 v t| A0 v n| A0 B v| | | | R| f]; unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *; rewrite computeEvalStrongRecHelp; unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *; simpl in |- *; rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ]; simpl in |- *.
unfold checkPrfAXM in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ]; simpl in |- *.
rewrite <- beq_nat_refl.
reflexivity.
set (C := cPair (cPair (cPair 1 (cPair (codeFormula L codeF codeR A0) (codeFormula L codeF codeR B))) (codePrf L codeF codeR Axm1 (fol.impH L A0 B) p1)) (cPair (codeFormula L codeF codeR A0) (codePrf L codeF codeR Axm2 A0 p0))) in *.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
unfold C at 1 in |- *.
unfold checkPrfMP in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
repeat rewrite evalStrongRecHelp1.
rewrite <- beq_nat_refl.
rewrite Hrecp0.
replace (cPair 1 (cPair (codeFormula L codeF codeR A0) (codeFormula L codeF codeR B))) with (codeFormula L codeF codeR (fol.impH L A0 B)); [ idtac | reflexivity ].
rewrite Hrecp1.
rewrite (wellFormedFormulaCorrect1 L codeF codeArityF codeArityFIsCorrect1 codeR codeArityR codeArityRIsCorrect1).
simpl in |- *.
replace (map (codeFormula L codeF codeR) (Axm1 ++ Axm2)) with (map (codeFormula L codeF codeR) Axm1 ++ map (codeFormula L codeF codeR) Axm2).
rewrite codeAppCorrect.
reflexivity.
generalize (codeFormula L codeF codeR); intro.
clear p1 A Hrecp1 Hrecp0 C.
induction Axm1 as [| a Axm1 HrecAxm1].
reflexivity.
simpl in |- *.
rewrite HrecAxm1.
reflexivity.
eapply lt_le_trans; [ idtac | apply cPairLe2 ].
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
unfold C in |- *.
apply cPairLe2.
eapply lt_le_trans; [ idtac | apply cPairLe2 ].
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
unfold C in |- *.
apply cPairLe1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
unfold checkPrfGEN in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
repeat rewrite evalStrongRecHelp1.
rewrite Hrecp.
unfold pred in |- *.
rewrite codeFreeVarListFormulaCorrect.
rewrite codeInCorrect.
induction (In_dec eq_nat_dec v (freeVarListFormula L Axm)).
elim n.
assumption.
replace (charFunction 2 beq_nat (cPair 3 (cPair v (codeFormula L codeF codeR A0))) (cPair 3 (cPair v (codeFormula L codeF codeR A0)))) with 1.
simpl in |- *.
reflexivity.
simpl in |- *.
rewrite <- beq_nat_refl.
reflexivity.
eapply lt_le_trans; [ idtac | apply cPairLe2 ].
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
unfold checkPrfIMP1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
unfold charFunction in |- *.
rewrite <- beq_nat_refl.
reflexivity.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
unfold checkPrfIMP2 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
unfold charFunction in |- *.
rewrite <- beq_nat_refl.
reflexivity.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
unfold checkPrfCP in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
unfold charFunction in |- *.
rewrite <- beq_nat_refl.
reflexivity.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
unfold checkPrfFA1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite codeSubFormulaCorrect.
unfold charFunction in |- *.
rewrite <- beq_nat_refl.
rewrite (wellFormedTermCorrect1 L codeF codeArityF codeArityFIsCorrect1).
reflexivity.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
unfold checkPrfFA2 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite codeFreeVarFormulaCorrect.
rewrite codeInCorrect.
induction (In_dec eq_nat_dec v (freeVarFormula L A0)).
elim n.
assumption.
unfold charFunction in |- *.
rewrite <- beq_nat_refl.
reflexivity.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
unfold checkPrfFA3 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
unfold charFunction in |- *.
rewrite <- beq_nat_refl.
reflexivity.
set (C := cPair 0 (cPair (codeTerm L codeF (fol.var L 0)) (codeTerm L codeF (fol.var L 0)))) in *.
unfold A at 1 in |- *.
cut (cPairPi1 (cPairPi2 (cPair C (cPair 9 0))) = 9); [ intro H; rewrite H; clear H | idtac ].
simpl in |- *.
unfold checkPrfEQ1 in |- *.
rewrite (cPairProjections2 C (cPair 9 0)).
rewrite (cPairProjections1 C (cPair 9 0)).
rewrite (cPairProjections2 9 0).
unfold C in |- *.
unfold charFunction in |- *.
rewrite <- beq_nat_refl.
simpl in |- *.
reflexivity.
rewrite (cPairProjections2 C (cPair 9 0)).
rewrite (cPairProjections1 9 0).
reflexivity.
set (C := cPair 1 (cPair (cPair 0 (cPair (codeTerm L codeF (fol.var L 0)) (codeTerm L codeF (fol.var L 1)))) (cPair 0 (cPair (codeTerm L codeF (fol.var L 1)) (codeTerm L codeF (fol.var L 0)))))) in *.
unfold A at 1 in |- *.
cut (cPairPi1 (cPairPi2 (cPair C (cPair 10 0))) = 10).
generalize (cPairPi1 (cPairPi2 (cPair C (cPair 10 0)))).
intros.
rewrite H.
simpl in |- *.
unfold checkPrfEQ2 in |- *.
replace (codeFormula L codeF codeR (fol.impH L (fol.equal L (fol.var L 0) (fol.var L 1)) (fol.equal L (fol.var L 1) (fol.var L 0)))) with C; [ idtac | reflexivity ].
generalize C; intros.
rewrite (cPairProjections2 C0 (cPair 10 0)).
rewrite (cPairProjections2 10 0).
rewrite (cPairProjections1 C0 (cPair 10 0)).
unfold charFunction in |- *.
repeat rewrite <- beq_nat_refl.
reflexivity.
rewrite (cPairProjections2 C (cPair 10 0)).
rewrite (cPairProjections1 10 0).
reflexivity.
set (C := cPair 1 (cPair (cPair 0 (cPair (codeTerm L codeF (fol.var L 0)) (codeTerm L codeF (fol.var L 1)))) (cPair 1 (cPair (cPair 0 (cPair (codeTerm L codeF (fol.var L 1)) (codeTerm L codeF (fol.var L 2)))) (cPair 0 (cPair (codeTerm L codeF (fol.var L 0)) (codeTerm L codeF (fol.var L 2)))))))) in *.
unfold A at 1 in |- *.
cut (cPairPi1 (cPairPi2 (cPair C (cPair 11 0))) = 11).
generalize (cPairPi1 (cPairPi2 (cPair C (cPair 11 0)))).
intros.
rewrite H.
simpl in |- *.
unfold checkPrfEQ3 in |- *.
replace (codeFormula L codeF codeR (fol.impH L (fol.equal L (fol.var L 0) (fol.var L 1)) (fol.impH L (fol.equal L (fol.var L 1) (fol.var L 2)) (fol.equal L (fol.var L 0) (fol.var L 2))))) with C; [ idtac | reflexivity ].
generalize C; intros.
rewrite (cPairProjections2 C0 (cPair 11 0)).
rewrite (cPairProjections1 C0 (cPair 11 0)).
rewrite (cPairProjections2 11 0).
unfold charFunction in |- *.
repeat rewrite <- beq_nat_refl.
reflexivity.
rewrite (cPairProjections2 C (cPair 11 0)).
rewrite (cPairProjections1 11 0).
reflexivity.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
unfold checkPrfEQ4 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite codeArityRIsCorrect1.
replace (codeAxmEqHelp (pred (S (arity L (inl (Functions L) R)))) (codeIff (cPair (S (S (S (S (codeR R))))) (codeNVars1 (pred (S (arity L (inl (Functions L) R)))))) (cPair (S (S (S (S (codeR R))))) (codeNVars2 (pred (S (arity L (inl (Functions L) R)))))))) with (codeFormula L codeF codeR (AxmEq4 L R)).
unfold charFunction in |- *.
repeat rewrite <- beq_nat_refl.
reflexivity.
unfold AxmEq4 in |- *.
clear A.
simpl in |- *.
induction (codeNVarsCorrect (arity L (inl (Functions L) R))).
rewrite H.
rewrite H0.
clear H H0.
induction (nVars L (arity L (inl (Functions L) R))).
simpl in |- *.
replace (codeIff (cPair (S (S (S (S (codeR R))))) (codeTerms L codeF (arity L (inl (Functions L) R)) a)) (cPair (S (S (S (S (codeR R))))) (codeTerms L codeF (arity L (inl (Functions L) R)) b))) with (codeFormula L codeF codeR (iffH L (fol.atomic L R a) (fol.atomic L R b))).
generalize (arity L (inl (Functions L) R)).
intros.
induction n as [| n Hrecn].
reflexivity.
simpl in |- *.
rewrite Hrecn.
reflexivity.
rewrite <- codeIffCorrect.
reflexivity.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
unfold checkPrfEQ5 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite codeArityFIsCorrect1.
replace (codeAxmEqHelp (pred (S (arity L (inr (Relations L) f)))) (cPair 0 (cPair (cPair (S (codeF f)) (codeNVars1 (pred (S (arity L (inr (Relations L) f)))))) (cPair (S (codeF f)) (codeNVars2 (pred (S (arity L (inr (Relations L) f))))))))) with (codeFormula L codeF codeR (AxmEq5 L f)).
unfold charFunction in |- *.
repeat rewrite <- beq_nat_refl.
reflexivity.
unfold AxmEq5 in |- *.
clear A.
simpl in |- *.
induction (codeNVarsCorrect (arity L (inr (Relations L) f))).
rewrite H.
rewrite H0.
clear H H0.
induction (nVars L (arity L (inr (Relations L) f))).
simpl in |- *.
replace (cPair 0 (cPair (cPair (S (codeF f)) (codeTerms L codeF (arity L (inr (Relations L) f)) a)) (cPair (S (codeF f)) (codeTerms L codeF (arity L (inr (Relations L) f)) b)))) with (codeFormula L codeF codeR (fol.equal L (fol.apply L f a) (fol.apply L f b))).
generalize (arity L (inr (Relations L) f)).
intros.
induction n as [| n Hrecn].
reflexivity.
simpl in |- *.
rewrite Hrecn.
reflexivity.
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
apply eqIsPR.

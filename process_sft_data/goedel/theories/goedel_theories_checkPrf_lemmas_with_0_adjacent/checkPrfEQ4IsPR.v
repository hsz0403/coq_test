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
apply multIsPR.

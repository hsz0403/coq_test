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

Lemma checkPrfCorrect2 : forall n m : nat, checkPrf n m <> 0 -> exists f : Formula, codeFormula L codeF codeR f = n /\ (exists l : list Formula, (exists p : Prf l f, codePrf L codeF codeR l f p = m)).
Proof.
assert (multLemma1 : forall a b : nat, a * b <> 0 -> a <> 0).
unfold not in |- *; intros.
apply H.
rewrite H0.
simpl in |- *.
reflexivity.
assert (multLemma2 : forall a b : nat, a * b <> 0 -> b <> 0).
intros.
rewrite mult_comm in H.
eapply multLemma1.
apply H.
assert (forall m n : nat, n < m -> checkPrf (cPairPi1 n) (cPairPi2 n) <> 0 -> exists f : Formula, (exists l : list Formula, (exists p : Prf l f, cPair (codeFormula L codeF codeR f) (codePrf L codeF codeR l f p) = n))).
intro.
induction m as [| m Hrecm].
intros.
elim (lt_n_O _ H).
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H)).
apply Hrecm; assumption.
unfold checkPrf in H0.
assert (wellFormedFormula (cPairPi1 n) <> 0).
destruct (wellFormedFormula (cPairPi1 n)).
assumption.
discriminate.
induction (wellFormedFormulaCorrect2 L codeF codeArityF codeArityFIsCorrect1 codeArityFIsCorrect2 codeR codeArityR codeArityRIsCorrect1 codeArityRIsCorrect2 _ H2).
exists x.
destruct (wellFormedFormula (cPairPi1 n)).
elim H2.
auto.
simpl in H0.
clear H2.
unfold checkPrfHelp in H0.
set (A := fun p recs : nat => switchPR (cPairPi1 (cPairPi2 p)) (switchPR (pred (cPairPi1 (cPairPi2 p))) (switchPR (pred (pred (cPairPi1 (cPairPi2 p)))) (switchPR (pred (pred (pred (cPairPi1 (cPairPi2 p))))) (switchPR (pred (pred (pred (pred (cPairPi1 (cPairPi2 p)))))) (switchPR (pred (pred (pred (pred (pred (cPairPi1 (cPairPi2 p))))))) (switchPR (pred (pred (pred (pred (pred (pred (cPairPi1 (cPairPi2 p)))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (cPairPi1 (cPairPi2 p))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (cPairPi1 (cPairPi2 p)))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (cPairPi1 (cPairPi2 p))))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (cPairPi1 (cPairPi2 p)))))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (cPairPi1 (cPairPi2 p))))))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (cPairPi1 (cPairPi2 p)))))))))))))) (switchPR (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (cPairPi1 (cPairPi2 p))))))))))))))) 0 (checkPrfEQ5 p recs)) (checkPrfEQ4 p recs)) (checkPrfEQ3 p recs)) (checkPrfEQ2 p recs)) (checkPrfEQ1 p recs)) (checkPrfFA3 p recs)) (checkPrfFA2 p recs)) (checkPrfFA1 p recs)) (checkPrfCP p recs)) (checkPrfIMP2 p recs)) (checkPrfIMP1 p recs)) (checkPrfGEN p recs)) (checkPrfMP p recs)) (checkPrfAXM p recs)) in *.
unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in H0; rewrite computeEvalStrongRecHelp in H0; unfold compose2, evalComposeFunc, evalOneParamList, evalList in H0; simpl in H0.
rewrite cPairProjections1 in H0.
assert (cPair (cPairPi1 (cPairPi2 n)) (cPairPi2 (cPairPi2 n)) = cPairPi2 n).
apply cPairProjections.
unfold A at 1 in H0.
repeat first [ rewrite cPairProjections1 in H0 | rewrite cPairProjections2 in H0 ].
destruct (cPairPi1 (cPairPi2 n)).
simpl in H0.
unfold checkPrfAXM in H0.
repeat first [ rewrite cPairProjections1 in H0 | rewrite cPairProjections2 in H0 ].
rewrite <- H3 in H0.
induction (eq_nat_dec (cPairPi2 (cPairPi2 n)) (codeFormula L codeF codeR x)).
exists (x :: nil).
exists (AXM L x).
rewrite H3.
simpl in |- *.
rewrite a in H2.
rewrite H2.
apply cPairProjections.
elim H0.
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
reflexivity.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfMP in H0.
repeat first [ rewrite cPairProjections1 in H0 | rewrite cPairProjections2 in H0 ].
assert (cPairPi2 (cPairPi2 n) < n).
apply lt_le_trans with (cPair 1 (cPairPi2 (cPairPi2 n))); [ idtac | rewrite H2; apply cPairLe2A ].
apply cPairLt2.
assert (cPairPi1 (cPairPi2 (cPairPi2 n)) < n).
apply le_lt_trans with (cPairPi2 (cPairPi2 n)).
apply cPairLe1A.
assumption.
assert (cPairPi2 (cPairPi2 (cPairPi2 n)) < n).
apply le_lt_trans with (cPairPi2 (cPairPi2 n)).
apply cPairLe2A.
assumption.
rewrite evalStrongRecHelp1 in H0.
rewrite evalStrongRecHelp1 in H0.
assert (wellFormedFormula (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))) <> 0).
unfold not in |- *; intros.
apply H0.
rewrite H7.
reflexivity.
induction (eq_nat_dec (cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 n)))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi1 n))).
induction (wellFormedFormulaCorrect2 L codeF codeArityF codeArityFIsCorrect1 codeArityFIsCorrect2 codeR codeArityR codeArityRIsCorrect1 codeArityRIsCorrect2 _ H7).
assert (checkPrf (cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 n)))) (cPairPi2 (cPairPi1 (cPairPi2 (cPairPi2 n)))) <> 0).
unfold checkPrf in |- *.
rewrite a.
rewrite <- H3.
rewrite <- H8.
rewrite codeImpCorrect.
rewrite (wellFormedFormulaCorrect1 L codeF codeArityF codeArityFIsCorrect1 codeR codeArityR codeArityRIsCorrect1).
simpl in |- *.
unfold checkPrfHelp in |- *.
fold A in |- *.
rewrite H8.
rewrite H3.
replace (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi1 n))) with (cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 n)))).
rewrite cPairProjections.
destruct (evalStrongRec 0 A (cPairPi1 (cPairPi2 (cPairPi2 n)))).
rewrite mult_comm in H0.
rewrite (mult_comm (charFunction 2 beq_nat (cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 n)))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi1 n)))) in H0.
simpl in H0.
assumption.
discriminate.
assert (checkPrf (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))) <> 0).
unfold checkPrf in |- *.
rewrite <- H8.
rewrite (wellFormedFormulaCorrect1 L codeF codeArityF codeArityFIsCorrect1 codeR codeArityR codeArityRIsCorrect1).
simpl in |- *.
unfold checkPrfHelp in |- *.
fold A in |- *.
rewrite H8.
rewrite cPairProjections.
destruct (evalStrongRec 0 A (cPairPi2 (cPairPi2 (cPairPi2 n)))).
rewrite mult_comm in H0.
rewrite (mult_comm (charFunction 2 beq_nat (cPairPi1 (cPairPi1 (cPairPi2 (cPairPi2 n)))) (codeImp (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi1 n)))) in H0.
rewrite (mult_comm (evalStrongRec 0 A (cPairPi1 (cPairPi2 (cPairPi2 n))))) in H0.
simpl in H0.
assumption.
discriminate.
assert (cPairPi1 (cPairPi2 (cPairPi2 n)) < m).
apply lt_le_trans with n.
assumption.
rewrite H1.
apply le_n.
assert (cPairPi2 (cPairPi2 (cPairPi2 n)) < m).
apply lt_le_trans with n.
assumption.
rewrite H1.
apply le_n.
induction (Hrecm _ H11 H9).
induction (Hrecm _ H12 H10).
induction H13 as (x3, H13).
induction H13 as (x4, H13).
induction H14 as (x5, H14).
induction H14 as (x6, H14).
exists (x3 ++ x5).
rewrite <- H13 in a.
rewrite <- H14 in a.
repeat rewrite cPairProjections1 in a.
rewrite <- H3 in a.
rewrite codeImpCorrect in a.
assert (x1 = impH x2 x).
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
assumption.
intros.
cut (cPair (codeFormula L codeF codeR x1) (codePrf L codeF codeR x3 x1 x4) = cPairPi1 (cPairPi2 (cPairPi2 n))).
generalize x4.
clear H13 x4.
rewrite H15.
intros.
exists (MP L x3 x5 x2 x x4 x6).
rewrite <- (cPairProjections n).
rewrite H3.
simpl in |- *.
rewrite <- H2.
replace (cPair 1 (cPair (codeFormula L codeF codeR x2) (codeFormula L codeF codeR x))) with (codeFormula L codeF codeR x1).
rewrite H14.
fold impH in |- *.
rewrite H15.
rewrite H13.
rewrite cPairProjections.
reflexivity.
assumption.
unfold charFunction in H0.
rewrite beq_nat_not_refl in H0.
rewrite mult_comm in H0.
simpl in H0.
elim H0.
reflexivity.
assumption.
rewrite cPairProjections.
assumption.
rewrite cPairProjections.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfGEN in H0.
repeat first [ rewrite cPairProjections1 in H0 | rewrite cPairProjections2 in H0 ].
assert (cPairPi2 (cPairPi2 (cPairPi2 n)) < n).
eapply le_lt_trans.
apply cPairLe2A.
apply lt_le_trans with (cPair 2 (cPairPi2 (cPairPi2 n))); [ idtac | rewrite H2; apply cPairLe2A ].
apply cPairLt2.
rewrite evalStrongRecHelp1 in H0.
induction (eq_nat_dec (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 n))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))))) (cPairPi1 n)).
rewrite <- a in H3.
destruct x as [t t0| r t| f f0| f| n1 f]; simpl in H3; try match goal with | H:(cPair ?X1 _ = cPair ?X2 _) |- _ => cut (X1 = X2); [ intro I; discriminate I | eapply cPairInj1; apply H ] end.
assert (n1 = cPairPi1 (cPairPi2 (cPairPi2 n))).
eapply cPairInj1.
eapply cPairInj2.
apply H3.
assert (codeFormula L codeF codeR f = cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))).
eapply cPairInj2.
eapply cPairInj2.
apply H3.
assert (checkPrf (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))) <> 0).
unfold checkPrf in |- *.
rewrite <- H6.
rewrite (wellFormedFormulaCorrect1 L codeF codeArityF codeArityFIsCorrect1 codeR codeArityR codeArityRIsCorrect1).
simpl in |- *.
unfold checkPrfHelp in |- *.
fold A in |- *.
rewrite H6.
rewrite cPairProjections.
destruct (evalStrongRec 0 A (cPairPi2 (cPairPi2 (cPairPi2 n)))).
rewrite mult_comm in H0.
simpl in H0.
assumption.
discriminate.
assert (cPairPi2 (cPairPi2 (cPairPi2 n)) < m).
apply lt_le_trans with n.
assumption.
rewrite H1.
apply le_n.
induction (Hrecm _ H8 H7).
induction H9 as (x0, H9).
induction H9 as (x1, H9).
exists x0.
rewrite <- H5 in H0.
rewrite <- H9 in H0.
assert (checkPrf (codeFormula L codeF codeR x) (codePrf L codeF codeR x0 x x1) = S (codeList (map (codeFormula L codeF codeR) x0))).
apply checkPrfCorrect1.
unfold checkPrf in H10.
rewrite (wellFormedFormulaCorrect1 L codeF codeArityF codeArityFIsCorrect1 codeR codeArityR codeArityRIsCorrect1) in H10.
simpl in H10.
unfold checkPrfHelp in H10.
fold A in H10.
rewrite H10 in H0.
unfold pred in H0.
rewrite codeFreeVarListFormulaCorrect in H0.
rewrite codeInCorrect in H0.
induction (In_dec eq_nat_dec n1 (freeVarListFormula L x0)).
rewrite (mult_comm (S (codeList (map (codeFormula L codeF codeR) x0)))) in H0.
rewrite mult_comm in H0.
simpl in H0.
elim H0; reflexivity.
rewrite <- H9 in H6.
rewrite cPairProjections1 in H6.
cut (cPair (codeFormula L codeF codeR x) (codePrf L codeF codeR x0 x x1) = cPairPi2 (cPairPi2 (cPairPi2 n))).
generalize x1.
clear H10 H0 x1 H9.
replace x with f.
intros.
exists (GEN L x0 f n1 b x1).
simpl in |- *.
rewrite H3.
rewrite a.
rewrite H0.
rewrite H5.
rewrite cPairProjections.
rewrite H2.
apply cPairProjections.
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
assumption.
assumption.
unfold charFunction in H0.
rewrite beq_nat_not_refl in H0.
elim H0.
simpl in |- *.
reflexivity.
assumption.
rewrite cPairProjections.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfIMP1 in H0.
repeat first [ rewrite cPairProjections1 in H0 | rewrite cPairProjections2 in H0 ].
exists (nil (A:=Formula)).
rewrite <- H3 in H0.
induction (eq_nat_dec (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 n))) (cPair 1 (cPair (cPairPi2 (cPairPi2 (cPairPi2 n))) (cPairPi1 (cPairPi2 (cPairPi2 n))))))) (codeFormula L codeF codeR x)).
destruct x as [t t0| r t| f f0| f| n1 f]; simpl in a; try match goal with | H:(cPair ?X1 _ = cPair ?X2 _) |- _ => cut (X1 = X2); [ intro I; discriminate I | eapply cPairInj1; apply H ] end.
assert (cPairPi1 (cPairPi2 (cPairPi2 n)) = codeFormula L codeF codeR f).
eapply cPairInj1.
eapply cPairInj2.
apply a.
assert (cPair 1 (cPair (cPairPi2 (cPairPi2 (cPairPi2 n))) (cPairPi1 (cPairPi2 (cPairPi2 n)))) = codeFormula L codeF codeR f0).
eapply cPairInj2.
eapply cPairInj2.
apply a.
clear a.
destruct f0 as [t t0| r t| f0 f1| f0| n1 f0]; simpl in H5; try match goal with | H:(cPair ?X1 _ = cPair ?X2 _) |- _ => cut (X1 = X2); [ intro I; discriminate I | eapply cPairInj1; apply H ] end.
assert (cPairPi2 (cPairPi2 (cPairPi2 n)) = codeFormula L codeF codeR f0).
eapply cPairInj1.
eapply cPairInj2.
apply H5.
assert (cPairPi1 (cPairPi2 (cPairPi2 n)) = codeFormula L codeF codeR f1).
eapply cPairInj2.
eapply cPairInj2.
apply H5.
assert (f1 = f).
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
transitivity (cPairPi1 (cPairPi2 (cPairPi2 n))).
symmetry in |- *.
assumption.
assumption.
rewrite H8.
rewrite H8 in H3.
exists (IMP1 L f f0).
rewrite H3.
simpl in |- *.
rewrite <- H4.
rewrite <- H6.
rewrite cPairProjections.
rewrite H2.
apply cPairProjections.
elim H0.
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
reflexivity.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfIMP2 in H0.
repeat first [ rewrite cPairProjections1 in H0 | rewrite cPairProjections2 in H0 ].
exists (nil (A:=Formula)).
clear A.
rewrite <- H3 in H0.
rename x into f.
induction (eq_nat_dec (cPair 1 (cPair (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 n))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))))))) (cPair 1 (cPair (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 n))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 n))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))))))))) (codeFormula L codeF codeR f)).
repeat match goal with | H:(cPair ?X1 (cPair ?X2 ?X3) = cPair ?X1 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair ?X1 (cPair _ _) = codeFormula L codeF codeR ?X2) |- _ => destruct X2; simpl in H; try match goal with | J:(cPair ?X1 _ = cPair ?X2 _) |- _ => cut (X1 = X2); [ intro I; discriminate I | eapply cPairInj1; apply J ] end end.
rewrite H3.
replace f2_2_1 with f1_1.
replace f1_2_2 with f2_2_2.
replace f1_2_1 with f2_1_2.
replace f2_1_1 with f1_1.
exists (IMP2 L f1_1 f2_1_2 f2_2_2).
simpl in |- *.
rewrite <- H9.
rewrite <- H8.
rewrite cPairProjections.
rewrite <- H6.
rewrite cPairProjections.
rewrite H2.
apply cPairProjections.
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
transitivity (cPairPi1 (cPairPi2 (cPairPi2 n))); [ symmetry in |- *; assumption | assumption ].
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
transitivity (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))); [ symmetry in |- *; assumption | assumption ].
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
transitivity (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))); [ symmetry in |- *; assumption | assumption ].
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
transitivity (cPairPi1 (cPairPi2 (cPairPi2 n))); [ symmetry in |- *; assumption | assumption ].
elim H0.
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
reflexivity.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfCP in H0.
clear A.
repeat first [ rewrite cPairProjections1 in H0 | rewrite cPairProjections2 in H0 ].
exists (nil (A:=Formula)).
rewrite <- H3 in H0.
rename x into f.
induction (eq_nat_dec (cPair 1 (cPair (cPair 1 (cPair (cPair 2 (cPairPi1 (cPairPi2 (cPairPi2 n)))) (cPair 2 (cPairPi2 (cPairPi2 (cPairPi2 n)))))) (cPair 1 (cPair (cPairPi2 (cPairPi2 (cPairPi2 n))) (cPairPi1 (cPairPi2 (cPairPi2 n))))))) (codeFormula L codeF codeR f)).
repeat match goal with | H:(cPair 1 (cPair ?X2 ?X3) = cPair 1 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair 2 ?X2 = cPair 2 ?X4) |- _ => assert (X2 = X4); [ eapply cPairInj2; apply H | clear H ] | H:(cPair ?X1 _ = codeFormula L codeF codeR ?X2) |- _ => destruct X2; simpl in H; try match goal with | J:(cPair ?X1 _ = cPair ?X2 _) |- _ => cut (X1 = X2); [ intro I; discriminate I | eapply cPairInj1; apply J ] end end.
rewrite H3.
replace f2_2 with f1_1.
replace f1_2 with f2_1.
exists (CP L f1_1 f2_1).
simpl in |- *.
rewrite <- H8.
rewrite <- H6.
rewrite cPairProjections.
rewrite H2.
apply cPairProjections.
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
transitivity (cPairPi2 (cPairPi2 (cPairPi2 n))); [ symmetry in |- *; assumption | assumption ].
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
transitivity (cPairPi1 (cPairPi2 (cPairPi2 n))); [ symmetry in |- *; assumption | assumption ].
elim H0.
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
reflexivity.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfFA1 in H0.
clear A.
repeat first [ rewrite cPairProjections1 in H0 | rewrite cPairProjections2 in H0 ].
exists (nil (A:=Formula)).
rewrite <- H3 in H0.
rename x into f.
induction (eq_nat_dec (cPair 1 (cPair (cPair 3 (cPair (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi1 (cPairPi2 (cPairPi2 n))))) (codeSubFormula (cPairPi1 (cPairPi2 (cPairPi2 n))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n))))))) (codeFormula L codeF codeR f)).
repeat match goal with | H:(cPair 1 (cPair ?X2 ?X3) = cPair 1 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair 3 (cPair ?X2 ?X3) = cPair 3 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair ?X1 _ = codeFormula L codeF codeR ?X2) |- _ => destruct X2; simpl in H; try match goal with | J:(cPair ?X1 _ = cPair ?X2 _) |- _ => cut (X1 = X2); [ intro I; discriminate I | eapply cPairInj1; apply J ] end end.
rewrite H3.
rewrite H6 in H5.
rewrite H7 in H5.
assert (wellFormedTerm (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))) <> 0).
eapply multLemma1.
apply H0.
induction (wellFormedTermCorrect2 L codeF codeArityF codeArityFIsCorrect1 codeArityFIsCorrect2 _ H4).
rewrite <- H8 in H5.
rewrite codeSubFormulaCorrect in H5.
replace f2 with (substituteFormula L f1 n1 x).
exists (FA1 L f1 n1 x).
simpl in |- *.
rewrite <- H7.
rewrite <- H6.
rewrite H8.
repeat rewrite cPairProjections.
rewrite H2.
apply cPairProjections.
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
assumption.
elim H0.
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
rewrite mult_comm.
reflexivity.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfFA2 in H0.
clear A.
repeat first [ rewrite cPairProjections1 in H0 | rewrite cPairProjections2 in H0 ].
exists (nil (A:=Formula)).
rewrite <- H3 in H0.
rename x into f.
induction (eq_nat_dec (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 n))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 n))) (cPairPi1 (cPairPi2 (cPairPi2 n))))))) (codeFormula L codeF codeR f)).
repeat match goal with | H:(cPair 1 (cPair ?X2 ?X3) = cPair 1 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair 3 (cPair ?X2 ?X3) = cPair 3 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair ?X1 _ = codeFormula L codeF codeR ?X2) |- _ => destruct X2; simpl in H; try match goal with | J:(cPair ?X1 _ = cPair ?X2 _) |- _ => cut (X1 = X2); [ intro I; discriminate I | eapply cPairInj1; apply J ] end end.
rewrite H3.
replace f2 with f1.
rewrite H6 in H0.
rewrite H4 in H0.
rewrite codeFreeVarFormulaCorrect in H0.
rewrite codeInCorrect in H0.
induction (In_dec eq_nat_dec n1 (freeVarFormula L f1)).
elim H0.
reflexivity.
exists (FA2 L f1 n1 b).
simpl in |- *.
rewrite <- H4.
rewrite <- H6.
rewrite cPairProjections.
rewrite H2.
apply cPairProjections.
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
transitivity (cPairPi1 (cPairPi2 (cPairPi2 n))); [ symmetry in |- *; assumption | assumption ].
elim H0.
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
rewrite mult_comm.
reflexivity.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfFA3 in H0.
clear A.
repeat first [ rewrite cPairProjections1 in H0 | rewrite cPairProjections2 in H0 ].
exists (nil (A:=Formula)).
rewrite <- H3 in H0.
rename x into f.
induction (eq_nat_dec (cPair 1 (cPair (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPair 1 (cPair (cPairPi1 (cPairPi2 (cPairPi2 n))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))))))) (cPair 1 (cPair (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi1 (cPairPi2 (cPairPi2 n))))) (cPair 3 (cPair (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))) (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))))))))) (codeFormula L codeF codeR f)).
repeat match goal with | H:(cPair 1 (cPair ?X2 ?X3) = cPair 1 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair 3 (cPair ?X2 ?X3) = cPair 3 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair ?X1 _ = codeFormula L codeF codeR ?X2) |- _ => destruct X2; simpl in H; try match goal with | J:(cPair ?X1 _ = cPair ?X2 _) |- _ => cut (X1 = X2); [ intro I; discriminate I | eapply cPairInj1; apply J ] end end.
rewrite H3.
replace f2_1 with f1_1.
replace f1_2 with f2_2.
replace n3 with n1.
replace n2 with n1.
exists (FA3 L f1_1 f2_2 n1).
simpl in |- *.
rewrite <- H4.
rewrite <- H8.
rewrite <- H5.
repeat rewrite cPairProjections.
rewrite H2.
apply cPairProjections.
transitivity (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))); [ symmetry in |- *; assumption | assumption ].
transitivity (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))); [ symmetry in |- *; assumption | assumption ].
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
transitivity (cPairPi1 (cPairPi2 (cPairPi2 (cPairPi2 n)))); [ symmetry in |- *; assumption | assumption ].
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
transitivity (cPairPi1 (cPairPi2 (cPairPi2 n))); [ symmetry in |- *; assumption | assumption ].
elim H0.
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
reflexivity.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfEQ1 in H0.
clear A.
exists (nil (A:=Formula)).
rewrite <- H3 in H0.
induction (eq_nat_dec (codeFormula L codeF codeR (fol.equal L (fol.var L 0) (fol.var L 0))) (codeFormula L codeF codeR x)).
rewrite H3.
replace x with (fol.equal L (fol.var L 0) (fol.var L 0)).
exists (EQ1 L).
simpl in |- *.
induction (eq_nat_dec (cPairPi2 (cPairPi2 n)) 0).
rewrite a0 in H2.
rewrite H2.
apply cPairProjections.
elim H0.
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
reflexivity.
rewrite cPairProjections2.
assumption.
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
assumption.
elim H0.
unfold charFunction in |- *.
rewrite (beq_nat_not_refl (codeFormula L codeF codeR (fol.equal L (fol.var L 0) (fol.var L 0)))) .
rewrite mult_comm.
reflexivity.
rewrite cPairProjections1.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfEQ2 in H0.
clear A.
exists (nil (A:=Formula)).
rewrite <- H3 in H0.
induction (eq_nat_dec (codeFormula L codeF codeR (fol.impH L (fol.equal L (fol.var L 0) (fol.var L 1)) (fol.equal L (fol.var L 1) (fol.var L 0)))) (codeFormula L codeF codeR x)).
rewrite H3.
replace x with (fol.impH L (fol.equal L (fol.var L 0) (fol.var L 1)) (fol.equal L (fol.var L 1) (fol.var L 0))).
exists (EQ2 L).
simpl in |- *.
induction (eq_nat_dec (cPairPi2 (cPairPi2 n)) 0).
rewrite a0 in H2.
rewrite H2.
apply cPairProjections.
elim H0.
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
reflexivity.
rewrite cPairProjections2.
assumption.
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
assumption.
elim H0.
unfold charFunction in |- *.
rewrite (beq_nat_not_refl (codeFormula L codeF codeR (fol.impH L (fol.equal L (fol.var L 0) (fol.var L 1)) (fol.equal L (fol.var L 1) (fol.var L 0))))) .
rewrite mult_comm.
reflexivity.
rewrite cPairProjections1.
assumption.
repeat rewrite <- pred_Sn in H0.
assert (H4 : forall n2 p q : nat, switchPR (S n2) p q = p).
simple destruct n2; trivial.
repeat rewrite H4 in H0.
clear H4.
destruct n1.
simpl in H0.
unfold checkPrfEQ3 in H0.
clear A.
exists (nil (A:=Formula)).
rewrite <- H3 in H0.
induction (eq_nat_dec (codeFormula L codeF codeR (fol.impH L (fol.equal L (fol.var L 0) (fol.var L 1)) (fol.impH L (fol.equal L (fol.var L 1) (fol.var L 2)) (fol.equal L (fol.var L 0) (fol.var L 2))))) (codeFormula L codeF codeR x)).
rewrite H3.
replace x with (fol.impH L (fol.equal L (fol.var L 0) (fol.var L 1)) (fol.impH L (fol.equal L (fol.var L 1) (fol.var L 2)) (fol.equal L (fol.var L 0) (fol.var L 2)))).
exists (EQ3 L).
simpl in |- *.
rewrite cPairProjections2 in H0.
rewrite cPairProjections1 in H0.
induction (eq_nat_dec (cPairPi2 (cPairPi2 n)) 0).
rewrite a0 in H2.
rewrite H2.
apply cPairProjections.
elim H0.
unfold charFunction in |- *.
rewrite beq_nat_not_refl.
reflexivity.
assumption.
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
assumption.
elim H0.
unfold charFunction in |- *.
rewrite (beq_nat_not_refl (codeFormula L codeF codeR (fol.impH L (fol.equal L (fol.var L 0) (fol.var L 1)) (fol.impH L (fol.equal L (fol.var L 1) (fol.var L 2)) (fol.equal L (fol.var L 0) (fol.var L 2)))))) .
rewrite mult_comm.
reflexivity.
rewrite cPairProjections1.
assumption.
destruct n1.
simpl in H0.
unfold checkPrfEQ4 in H0.
clear A.
repeat rewrite cPairProjections2 in H0.
repeat rewrite cPairProjections1 in H0.
exists (nil (A:=Formula)).
rewrite <- H3 in H0.
assert (codeArityR (cPairPi2 (cPairPi2 n)) <> 0).
unfold notZero in H0.
unfold not in |- *; intros.
rewrite H4 in H0.
apply H0.
reflexivity.
induction (codeArityRIsCorrect2 _ H4).
rewrite <- H5 in H0.
rewrite codeArityRIsCorrect1 in H0.
simpl in H0.
induction (codeNVarsCorrect (arity L (inl (Functions L) x0))).
rewrite H6 in H0.
rewrite H7 in H0.
clear H6 H7.
assert (codeIff (cPair (S (S (S (S (codeR x0))))) (codeTerms L codeF (arity L (inl (Functions L) x0)) (fst (nVars L (arity L (inl (Functions L) x0)))))) (cPair (S (S (S (S (codeR x0))))) (codeTerms L codeF (arity L (inl (Functions L) x0)) (snd (nVars L (arity L (inl (Functions L) x0)))))) = codeIff (codeFormula L codeF codeR (atomic x0 (fst (nVars L (arity L (inl (Functions L) x0)))))) (codeFormula L codeF codeR (atomic x0 (snd (nVars L (arity L (inl (Functions L) x0))))))).
reflexivity.
rewrite H6 in H0.
clear H6.
rewrite codeIffCorrect in H0.
assert (AxmEq4 L x0 = x).
clear H5.
unfold AxmEq4 in |- *.
induction (nVars L (arity L (inl (Functions L) x0))).
simpl in |- *.
unfold fst, snd in H0.
cut ((if beq_nat (codeAxmEqHelp (arity L (inl (Functions L) x0)) (codeFormula L codeF codeR (iffH L (atomic x0 a) (atomic x0 b)))) (codeFormula L codeF codeR x) then 1 else 0) + 0 <> 0).
fold atomic in |- *.
generalize (iffH L (atomic x0 a) (atomic x0 b)).
intros.
clear H0.
clear a b.
cut (codeAxmEqHelp (arity L (inl (Functions L) x0)) (codeFormula L codeF codeR f) = codeFormula L codeF codeR x).
generalize x.
clear H5.
induction (arity L (inl (Functions L) x0)); simpl in |- *; intros.
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
assumption.
rename x1 into f0.
repeat match goal with | H:(cPair 1 (cPair ?X2 ?X3) = cPair 1 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair 0 (cPair ?X2 ?X3) = cPair 0 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair ?X1 _ = codeFormula L codeF codeR ?X2) |- _ => destruct X2; simpl in H; try match goal with | J:(cPair ?X1 _ = cPair ?X2 _) |- _ => cut (X1 = X2); [ intro I; discriminate I | eapply cPairInj1; apply J ] end end.
rewrite (IHn1 f0_2).
destruct t.
replace n2 with (n1 + n1).
destruct t0.
replace n3 with (S (n1 + n1)).
reflexivity.
apply cPairInj2 with 0 0.
apply H7.
elim O_S with (codeF f0).
apply cPairInj1 with (S (n1 + n1)) (codeTerms L codeF (arity L (inr (Relations L) f0)) t).
apply H7.
apply cPairInj2 with 0 0.
apply H0.
elim O_S with (codeF f0).
apply cPairInj1 with (n1 + n1) (codeTerms L codeF (arity L (inr (Relations L) f0)) t).
apply H0.
assumption.
induction (eq_nat_dec (codeAxmEqHelp (arity L (inl (Functions L) x0)) (codeFormula L codeF codeR f)) (codeFormula L codeF codeR x)).
assumption.
elim H5.
rewrite beq_nat_not_refl.
reflexivity.
assumption.
assumption.
rewrite H3.
rewrite <- H6.
exists (EQ4 L x0).
simpl in |- *.
rewrite H5.
rewrite H2.
apply cPairProjections.
destruct n1.
simpl in H0.
unfold checkPrfEQ5 in H0.
clear A.
repeat rewrite cPairProjections2 in H0.
repeat rewrite cPairProjections1 in H0.
exists (nil (A:=Formula)).
rewrite <- H3 in H0.
assert (codeArityF (cPairPi2 (cPairPi2 n)) <> 0).
unfold notZero in H0.
unfold not in |- *; intros.
rewrite H4 in H0.
apply H0.
reflexivity.
induction (codeArityFIsCorrect2 _ H4).
rewrite <- H5 in H0.
rewrite codeArityFIsCorrect1 in H0.
simpl in H0.
induction (codeNVarsCorrect (arity L (inr (Relations L) x0))).
rewrite H6 in H0.
rewrite H7 in H0.
clear H6 H7.
assert (cPair 0 (cPair (cPair (S (codeF x0)) (codeTerms L codeF (arity L (inr (Relations L) x0)) (fst (nVars L (arity L (inr (Relations L) x0)))))) (cPair (S (codeF x0)) (codeTerms L codeF (arity L (inr (Relations L) x0)) (snd (nVars L (arity L (inr (Relations L) x0))))))) = codeFormula L codeF codeR (equal (apply x0 (fst (nVars L (arity L (inr (Relations L) x0))))) (apply x0 (snd (nVars L (arity L (inr (Relations L) x0))))))).
reflexivity.
rewrite H6 in H0.
clear H6.
assert (AxmEq5 L x0 = x).
clear H5.
unfold AxmEq5 in |- *.
induction (nVars L (arity L (inr (Relations L) x0))).
simpl in |- *.
unfold fst, snd in H0.
cut ((if beq_nat (codeAxmEqHelp (arity L (inr (Relations L) x0)) (codeFormula L codeF codeR (equal (apply x0 a) (apply x0 b)))) (codeFormula L codeF codeR x) then 1 else 0) + 0 <> 0).
fold apply equal in |- *.
generalize (equal (apply x0 a) (apply x0 b)).
intros.
clear H0.
clear a b.
cut (codeAxmEqHelp (arity L (inr (Relations L) x0)) (codeFormula L codeF codeR f) = codeFormula L codeF codeR x).
generalize x.
clear H5.
induction (arity L (inr (Relations L) x0)); simpl in |- *; intros.
apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
assumption.
repeat match goal with | H:(cPair 1 (cPair ?X2 ?X3) = cPair 1 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair 0 (cPair ?X2 ?X3) = cPair 0 (cPair ?X4 ?X5)) |- _ => assert (X2 = X4); [ eapply cPairInj1; eapply cPairInj2; apply H | assert (X3 = X5); [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ] | H:(cPair ?X1 _ = codeFormula L codeF codeR ?X2) |- _ => destruct X2; simpl in H; try match goal with | J:(cPair ?X1 _ = cPair ?X2 _) |- _ => cut (X1 = X2); [ intro I; discriminate I | eapply cPairInj1; apply J ] end end.
rewrite (IHn1 x1_2).
destruct t.
replace n2 with (n1 + n1).
destruct t0.
replace n3 with (S (n1 + n1)).
reflexivity.
apply cPairInj2 with 0 0.
apply H7.
elim O_S with (codeF f0).
apply cPairInj1 with (S (n1 + n1)) (codeTerms L codeF (arity L (inr (Relations L) f0)) t).
apply H7.
apply cPairInj2 with 0 0.
apply H0.
elim O_S with (codeF f0).
apply cPairInj1 with (n1 + n1) (codeTerms L codeF (arity L (inr (Relations L) f0)) t).
apply H0.
assumption.
induction (eq_nat_dec (codeAxmEqHelp (arity L (inr (Relations L) x0)) (codeFormula L codeF codeR f)) (codeFormula L codeF codeR x)).
assumption.
elim H5.
rewrite beq_nat_not_refl.
reflexivity.
assumption.
assumption.
rewrite H3.
rewrite <- H6.
exists (EQ5 L x0).
simpl in |- *.
rewrite H5.
rewrite H2.
apply cPairProjections.
elim H0.
simpl in |- *.
reflexivity.
intros.
assert (exists f : Formula, (exists l : list Formula, (exists p : Prf l f, cPair (codeFormula L codeF codeR f) (codePrf L codeF codeR l f p) = cPair n m))).
eapply H.
apply lt_n_Sn.
rewrite cPairProjections1.
rewrite cPairProjections2.
assumption.
decompose record H1.
exists x.
split.
eapply cPairInj1.
apply H2.
exists x0.
exists x1.
eapply cPairInj2.
apply H2.

Require Import Arith.
Require Import fol.
Require Import folProof.
Require Import cPair.
Section Code_Term_Formula_Proof.
Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.
Hypothesis codeFInj : forall f g : Functions L, codeF f = codeF g -> f = g.
Hypothesis codeRInj : forall R S : Relations L, codeR R = codeR S -> R = S.
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
Let Prf := Prf L.
Let SysPrf := SysPrf L.
Fixpoint codeTerm (t : Term) : nat := match t with | fol.var n => cPair 0 n | fol.apply f ts => cPair (S (codeF f)) (codeTerms _ ts) end with codeTerms (n : nat) (ts : Terms n) {struct ts} : nat := match ts with | Tnil => 0 | Tcons n t ss => S (cPair (codeTerm t) (codeTerms n ss)) end.
Fixpoint codeFormula (f : Formula) : nat := match f with | fol.equal t1 t2 => cPair 0 (cPair (codeTerm t1) (codeTerm t2)) | fol.impH f1 f2 => cPair 1 (cPair (codeFormula f1) (codeFormula f2)) | fol.notH f1 => cPair 2 (codeFormula f1) | fol.forallH n f1 => cPair 3 (cPair n (codeFormula f1)) | fol.atomic R ts => cPair (4+(codeR R)) (codeTerms _ ts) end.
Fixpoint codePrf (Z : Formulas) (f : Formula) (prf : Prf Z f) {struct prf} : nat := match prf with | AXM A => cPair 0 (codeFormula A) | MP Axm1 Axm2 A B rec1 rec2 => cPair 1 (cPair (cPair (cPair 1 (cPair (codeFormula A) (codeFormula B))) (codePrf _ _ rec1)) (cPair (codeFormula A) (codePrf _ _ rec2))) | GEN Axm A v _ rec => cPair 2 (cPair v (cPair (codeFormula A) (codePrf _ _ rec))) | IMP1 A B => cPair 3 (cPair (codeFormula A) (codeFormula B)) | IMP2 A B C => cPair 4 (cPair (codeFormula A) (cPair (codeFormula B) (codeFormula C))) | CP A B => cPair 5 (cPair (codeFormula A) (codeFormula B)) | FA1 A v t => cPair 6 (cPair (codeFormula A) (cPair v (codeTerm t))) | FA2 A v _ => cPair 7 (cPair (codeFormula A) v) | FA3 A B v => cPair 8 (cPair (codeFormula A) (cPair (codeFormula B) v)) | EQ1 => cPair 9 0 | EQ2 => cPair 10 0 | EQ3 => cPair 11 0 | EQ4 r => cPair 12 (codeR r) | EQ5 f => cPair 13 (codeF f) end.
Definition codeImp (a b : nat) := cPair 1 (cPair a b).
Definition codeNot (a : nat) := cPair 2 a.
Definition codeForall (n a : nat) := cPair 3 (cPair n a).
Definition codeOr (a b : nat) := codeImp (codeNot a) b.
Definition codeAnd (a b : nat) := codeNot (codeOr (codeNot a) (codeNot b)).
Definition codeIff (a b : nat) := codeAnd (codeImp a b) (codeImp b a).
End Code_Term_Formula_Proof.

Lemma codeImpCorrect : forall a b : Formula, codeImp (codeFormula a) (codeFormula b) = codeFormula (impH a b).
Proof.
auto.

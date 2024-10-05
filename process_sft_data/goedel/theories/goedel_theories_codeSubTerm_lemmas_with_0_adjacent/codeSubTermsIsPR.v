Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import folProp.
Require Import code.
Require Import extEqualNat.
Require Vector.
Section Code_Substitute_Term.
Variable L : Language.
Variable codeF : Functions L -> nat.
Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Definition codeSubTermTerms : nat -> nat -> nat -> nat := evalStrongRec 2 (fun t recs v s : nat => cPair (switchPR (cPairPi1 t) (cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))) (switchPR (charFunction 2 beq_nat (cPairPi2 t) v) s t)) (switchPR t (S (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0)).
Definition codeSubTerm (t s v : nat) : nat := cPairPi1 (codeSubTermTerms t s v).
Definition codeSubTerms (t s v : nat) : nat := cPairPi2 (codeSubTermTerms t s v).
End Code_Substitute_Term.

Lemma codeSubTermsIsPR : isPR 3 codeSubTerms.
Proof.
unfold codeSubTerms in |- *.
apply compose3_1IsPR.
apply codeSubTermTermsIsPR.
apply cPairPi2IsPR.

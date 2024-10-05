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

Lemma codeSubTermTermsIsPR : isPR 3 codeSubTermTerms.
Proof.
unfold codeSubTermTerms in |- *.
apply evalStrongRecIsPR.
apply compose4_2IsPR with (f1 := fun t recs v s : nat => switchPR (cPairPi1 t) (cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))) (switchPR (charFunction 2 beq_nat (cPairPi2 t) v) s t)) (f2 := fun t recs v s : nat => switchPR t (S (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0).
apply compose4_3IsPR with (f1 := fun t recs v s : nat => cPairPi1 t) (f2 := fun t recs v s : nat => cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))) (f3 := fun t recs v s : nat => switchPR (charFunction 2 beq_nat (cPairPi2 t) v) s t).
apply filter1000IsPR with (g := cPairPi1).
apply cPairPi1IsPR.
apply filter1100IsPR with (g := fun t recs : nat => cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))).
apply compose2_2IsPR with (f := fun t recs : nat => cPairPi1 t) (g := fun t recs : nat => cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)).
apply filter10IsPR with (g := cPairPi1).
apply cPairPi1IsPR.
apply compose2_1IsPR with (f := fun t recs : nat => codeNth (t - S (cPairPi2 t)) recs).
apply compose2_2IsPR with (f := fun t recs : nat => t - S (cPairPi2 t)) (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (cPairPi2 t)).
apply compose1_2IsPR with (f := fun t : nat => t) (f' := fun t : nat => S (cPairPi2 t)).
apply idIsPR.
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply cPairPi2IsPR.
apply cPairIsPR.
apply filter1011IsPR with (g := fun t v s : nat => switchPR (charFunction 2 beq_nat (cPairPi2 t) v) s t).
apply compose3_3IsPR with (f1 := fun t v s : nat => charFunction 2 beq_nat (cPairPi2 t) v) (f2 := fun t v s : nat => s) (f3 := fun t v s : nat => t).
apply filter110IsPR with (g := fun t v : nat => charFunction 2 beq_nat (cPairPi2 t) v).
apply compose2_2IsPR with (f := fun t v : nat => cPairPi2 t) (g := fun t v : nat => v).
apply filter10IsPR.
apply cPairPi2IsPR.
apply pi2_2IsPR.
apply eqIsPR.
apply pi3_3IsPR.
apply pi1_3IsPR.
apply switchIsPR.
apply switchIsPR.
apply filter1100IsPR with (g := fun t recs : nat => switchPR t (S (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0).
apply compose2_3IsPR with (f1 := fun t recs : nat => t) (f2 := fun t recs : nat => S (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) (f3 := fun t recs : nat => 0).
apply pi1_2IsPR.
apply compose2_1IsPR with (f := fun t recs : nat => cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs))).
assert (forall g : nat -> nat, isPR 1 g -> isPR 2 (fun t recs : nat => g (codeNth (t - S (g (pred t))) recs))).
intros.
apply compose2_1IsPR with (f := fun t recs : nat => codeNth (t - S (g (pred t))) recs).
apply compose2_2IsPR with (f := fun t recs : nat => t - S (g (pred t))) (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (g (pred t))).
apply compose1_2IsPR with (f := fun t : nat => t) (f' := fun t : nat => S (g (pred t))).
apply idIsPR.
apply compose1_1IsPR with (f := fun t : nat => g (pred t)).
apply compose1_1IsPR.
apply predIsPR.
auto.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
auto.
apply compose2_2IsPR with (f := fun t recs : nat => cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (g := fun t recs : nat => cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)).
apply H.
apply cPairPi1IsPR.
apply H.
apply cPairPi2IsPR.
apply cPairIsPR.
apply succIsPR.
exists (composeFunc 2 0 (PRnil _) zeroFunc).
simpl in |- *.
auto.
apply switchIsPR.
apply cPairIsPR.

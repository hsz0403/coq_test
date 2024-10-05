Require Import primRec.
Require Import cPair.
Require Export Coq.Lists.List.
Require Import ListExt.
Require Import Arith.
Require Vector.
Require Import extEqualNat.
Definition codeLength : nat -> nat := evalStrongRec 0 (fun n Hrecs : nat => switchPR n (S (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0).
Definition codeApp : nat -> nat -> nat := evalStrongRec 1 (fun n Hrecs p1 : nat => switchPR n (S (cPair (cPairPi1 (pred n)) (codeNth (n - S (cPairPi2 (pred n))) Hrecs))) p1).
Definition codeListRemove (a l : nat) : nat := evalStrongRec 1 (fun n Hrecs p1 : nat => switchPR n (switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1) (codeNth (n - S (cPairPi2 (pred n))) Hrecs) (S (cPair (cPairPi1 (pred n)) (codeNth (n - S (cPairPi2 (pred n))) Hrecs)))) (codeList nil)) l a.
Definition codeIn (a l : nat) : nat := evalStrongRec 1 (fun n Hrecs p1 : nat => switchPR n (switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1) 1 (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) l a.
Definition codeNoDup : nat -> nat := evalStrongRec 0 (fun l recs : nat => switchPR l (switchPR (codeIn (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs)) (codeNth (l - S (cPairPi2 (pred l))) recs) (S (cPair (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs)))) 0).

Lemma codeInIsPR : isPR 2 codeIn.
Proof.
unfold codeIn in |- *.
apply swapIsPR.
apply evalStrongRecIsPR.
apply compose3_3IsPR with (g := switchPR) (f1 := fun n Hrecs p1 : nat => n) (f2 := fun n Hrecs p1 : nat => switchPR (charFunction 2 beq_nat (cPairPi1 (pred n)) p1) 1 (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) (f3 := fun n Hrecs p1 : nat => 0).
apply pi1_3IsPR.
apply compose3_3IsPR with (g := switchPR) (f1 := fun n Hrecs p1 : nat => charFunction 2 beq_nat (cPairPi1 (pred n)) p1) (f2 := fun n Hrecs p1 : nat => 1) (f3 := fun n Hrecs p1 : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
apply filter101IsPR with (g := fun n p1 : nat => charFunction 2 beq_nat (cPairPi1 (pred n)) p1).
apply compose2_2IsPR with (h := charFunction 2 beq_nat) (f := fun n p1 : nat => cPairPi1 (pred n)) (g := fun n p1 : nat => p1).
apply filter10IsPR with (g := fun n : nat => cPairPi1 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
apply pi2_2IsPR.
apply eqIsPR.
apply filter100IsPR with (g := fun _ : nat => 1).
apply const1_NIsPR.
apply filter110IsPR with (g := fun n Hrecs : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
apply compose2_2IsPR with (h := codeNth) (f := fun n Hrecs : nat => n - S (cPairPi2 (pred n))) (g := fun n Hrecs : nat => Hrecs).
apply filter10IsPR with (g := fun n : nat => n - S (cPairPi2 (pred n))).
apply compose1_2IsPR with (g := minus) (f := fun n : nat => n) (f' := fun n : nat => S (cPairPi2 (pred n))).
apply idIsPR.
apply compose1_1IsPR with (g := S) (f := fun n : nat => cPairPi2 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply switchIsPR.
apply filter100IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply switchIsPR.

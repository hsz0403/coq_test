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

Lemma codeLengthIsPR : isPR 1 codeLength.
Proof.
unfold codeLength in |- *.
apply evalStrongRecIsPR.
apply compose2_3IsPR with (f1 := fun n Hrecs : nat => n) (f2 := fun n Hrecs : nat => S (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) (f3 := fun n Hrecs : nat => 0).
apply pi1_2IsPR.
apply compose2_1IsPR with (f := fun n Hrecs : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
apply compose2_2IsPR with (f := fun n Hrecs : nat => n - S (cPairPi2 (pred n))) (g := fun n Hrecs : nat => Hrecs).
apply filter10IsPR with (g := fun n : nat => n - S (cPairPi2 (pred n))).
apply compose1_2IsPR with (f := fun n : nat => n) (f' := fun n : nat => S (cPairPi2 (pred n))).
apply idIsPR.
apply compose1_1IsPR with (f := fun n : nat => cPairPi2 (pred n)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply succIsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply switchIsPR.

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

Lemma codeNoDupIsPR : isPR 1 codeNoDup.
Proof.
unfold codeNoDup in |- *.
apply evalStrongRecIsPR.
apply compose2_3IsPR with (f1 := fun l recs : nat => l) (f2 := fun l recs : nat => switchPR (codeIn (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs)) (codeNth (l - S (cPairPi2 (pred l))) recs) (S (cPair (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs)))) (f3 := fun l recs : nat => 0).
apply pi1_2IsPR.
assert (isPR 2 (fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs)).
apply callIsPR with (g := fun l : nat => cPairPi2 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi2IsPR.
apply compose2_3IsPR with (f1 := fun l recs : nat => codeIn (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs)) (f2 := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs) (f3 := fun l recs : nat => S (cPair (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs))).
apply compose2_2IsPR with (f := fun l recs : nat => cPairPi1 (pred l)) (g := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs).
apply filter10IsPR with (g := fun l : nat => cPairPi1 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
assumption.
apply codeInIsPR.
assumption.
apply compose2_1IsPR with (f := fun l recs : nat => cPair (cPairPi1 (pred l)) (codeNth (l - S (cPairPi2 (pred l))) recs)).
apply compose2_2IsPR with (f := fun l recs : nat => cPairPi1 (pred l)) (g := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs).
apply filter10IsPR with (g := fun l : nat => cPairPi1 (pred l)).
apply compose1_1IsPR.
apply predIsPR.
apply cPairPi1IsPR.
assumption.
apply cPairIsPR.
apply succIsPR.
apply switchIsPR.
apply filter10IsPR with (g := fun _ : nat => 0).
apply const1_NIsPR.
apply switchIsPR.

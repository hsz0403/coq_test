Require Import primRec.
Require Import code.
Require Import Arith.
Require Import cPair.

Lemma codeForallIsPR : isPR 2 (fun a b : nat => cPair 3 (cPair a b)).
Proof.
apply compose2_2IsPR with (f := fun a b : nat => 3).
apply filter10IsPR with (g := fun _ : nat => 3).
apply const1_NIsPR.
apply cPairIsPR.
apply cPairIsPR.

Require Import primRec.
Require Import code.
Require Import Arith.
Require Import cPair.

Lemma codeImpIsPR : isPR 2 codeImp.
Proof.
unfold codeImp in |- *.
apply compose2_2IsPR with (f := fun a b : nat => 1).
apply filter10IsPR with (g := fun _ : nat => 1).
apply const1_NIsPR.
apply cPairIsPR.
apply cPairIsPR.

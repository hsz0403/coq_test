Require Import primRec.
Require Import code.
Require Import Arith.
Require Import cPair.

Lemma codeNotIsPR : isPR 1 codeNot.
Proof.
unfold codeNot in |- *.
apply compose1_2IsPR with (f := fun a : nat => 2) (f' := fun a : nat => a).
apply const1_NIsPR.
apply idIsPR.
apply cPairIsPR.

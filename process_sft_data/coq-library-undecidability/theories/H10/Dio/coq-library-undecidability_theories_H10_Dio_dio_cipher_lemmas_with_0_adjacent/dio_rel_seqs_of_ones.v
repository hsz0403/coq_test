Require Import Arith List Bool.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac gcd prime binomial sums bool_nat.
From Undecidability.H10.Matija Require Import cipher.
From Undecidability.H10.Dio Require Import dio_logic dio_expo dio_binary.
Set Implicit Arguments.
Local Infix "≲" := binary_le (at level 70, no associativity).
Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).
Local Infix "⇣" := nat_meet (at level 40, left associativity).
Local Infix "⇡" := nat_join (at level 50, left associativity).

Theorem dio_rel_seqs_of_ones l q u u1 : 𝔻F l -> 𝔻F q -> 𝔻F u -> 𝔻F u1 -> 𝔻R (fun v => seqs_of_ones (l v) (q v) (u v) (u1 v)).
Proof.
dio by lemma (fun v => seqs_of_ones_dio (l v) (q v) (u v) (u1 v)).

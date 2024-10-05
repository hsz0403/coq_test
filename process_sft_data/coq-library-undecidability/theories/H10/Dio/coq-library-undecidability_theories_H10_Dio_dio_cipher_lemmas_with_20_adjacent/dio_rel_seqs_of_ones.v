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

Theorem dio_rel_Code l q a : 𝔻F l -> 𝔻F q -> 𝔻F a -> 𝔻R (fun v => Code (l v) (q v) (a v)).
Proof.
Admitted.

Theorem dio_rel_Const l q c x : 𝔻F l -> 𝔻F q -> 𝔻F c -> 𝔻F x -> 𝔻R (fun v => Const (l v) (q v) (c v) (x v)).
Proof.
Admitted.

Theorem dio_rel_CodeNat l q a : 𝔻F l -> 𝔻F q -> 𝔻F a -> 𝔻R (fun v => CodeNat (l v) (q v) (a v)).
Proof.
Admitted.

Theorem dio_rel_Code_plus a b c : 𝔻F a -> 𝔻F b -> 𝔻F c -> 𝔻R (fun v => Code_plus (a v) (b v) (c v)).
Proof.
Admitted.

Theorem dio_rel_Code_mult l q a b c : 𝔻F l -> 𝔻F q -> 𝔻F a -> 𝔻F b -> 𝔻F c -> 𝔻R (fun v => Code_mult (l v) (q v) (a v) (b v) (c v)).
Proof.
Admitted.

Theorem dio_rel_seqs_of_ones l q u u1 : 𝔻F l -> 𝔻F q -> 𝔻F u -> 𝔻F u1 -> 𝔻R (fun v => seqs_of_ones (l v) (q v) (u v) (u1 v)).
Proof.
dio by lemma (fun v => seqs_of_ones_dio (l v) (q v) (u v) (u1 v)).

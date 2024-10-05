Require Import Arith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_nat gcd crt sums.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.MuRec Require Import recomp.
Set Implicit Arguments.
Definition beta a n := godel_beta (decomp_l a) (decomp_r a) n.

Lemma beta_inv n (v : vec _ n) : { a | forall p, beta a (pos2nat p) = vec_pos v p }.
Proof.
destruct (godel_beta_inv v) as (a & b & H).
exists (recomp a b); intro p; unfold beta.
rewrite decomp_l_recomp, decomp_r_recomp; auto.

Require Import Arith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_nat gcd crt sums.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.MuRec Require Import recomp.
Set Implicit Arguments.
Definition beta a n := godel_beta (decomp_l a) (decomp_r a) n.

Lemma beta_fun_inv n f : { a | forall p, p < n -> f p = beta a p }.
Proof.
destruct beta_inv with (v := vec_set_pos (fun p : pos n => f (pos2nat p))) as (a & Ha).
exists a; intros p Hp.
specialize (Ha (nat2pos Hp)).
rewrite vec_pos_set, pos2nat_nat2pos in Ha.
auto.

Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive RInt Continuity Lim_seq ElemFct RInt_analysis.
Ltac pos_rat := repeat ( apply Rdiv_lt_0_compat || apply Rplus_lt_0_compat || apply Rmult_lt_0_compat) ; try by apply Rlt_0_1.
Definition fab (a b x : R) : R := (a + b * ln x) / x.
Definition f (x : R) : R := fab 2 2 x.
Fixpoint u (n : nat) : R := match n with | O => 2 | S n => 2/3 * u n + 1/3 * (INR n) + 1 end.
Definition v (n : nat) : R := u n - INR n.
Definition Su (n : nat) : R := sum_f_R0 u n.
Definition Tu (n : nat) : R := Su n / (INR n) ^ 2.

Lemma Val_a_b (a b : R) : fab a b 1 = 2 -> Derive (fab a b) 1 = 0 -> a = 2 /\ b = 2.
Proof.
move => Hf Hdf.
rewrite /fab in Hf.
rewrite ln_1 in Hf.
rewrite Rdiv_1 in Hf.
rewrite Rmult_0_r in Hf.
rewrite Rplus_0_r in Hf.
rewrite Hf in Hdf |- * => {a Hf}.
split.
reflexivity.
replace (Derive (fab 2 b) 1) with (((b - 2) - b * ln 1) / 1 ^ 2) in Hdf.
rewrite ln_1 /= in Hdf.
field_simplify in Hdf.
rewrite !Rdiv_1 in Hdf.
by apply Rminus_diag_uniq.
apply sym_eq, is_derive_unique.
apply Dfab.
by apply Rlt_0_1.

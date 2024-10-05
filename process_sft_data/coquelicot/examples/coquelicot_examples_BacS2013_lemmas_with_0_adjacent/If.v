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

Lemma If : forall x, 0 < x -> is_derive (fun y : R => 2 * ln y + (ln y) ^ 2) x (f x).
Proof.
move => y Hy.
evar_last.
apply @is_derive_plus.
apply is_derive_Reals.
apply derivable_pt_lim_scal.
by apply derivable_pt_lim_ln.
apply is_derive_pow.
by apply is_derive_Reals, derivable_pt_lim_ln.
rewrite /f /fab /plus /= ; field.
by apply Rgt_not_eq.

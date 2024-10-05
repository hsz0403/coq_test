Require Import Reals Omega mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Continuity Derive Hierarchy RInt PSeries.
Require Import Lim_seq RInt_analysis.
Section nat_to_ring.
Context {K : Ring}.
Definition nat_to_ring (n : nat) : K := sum_n_m (fun _ => one) 1 n.
End nat_to_ring.
Section is_derive_mult.
Context {K : AbsRing}.
End is_derive_mult.

Lemma is_derive_n_pow_smalli: forall i p x, (i <= p)%nat -> is_derive_n (fun x : R => x ^ p) i x (INR (fact p) / INR (fact (p - i)%nat) * x ^ (p - i)%nat).
Proof.
elim => /= [ | i IH] p x Hip.
rewrite -minus_n_O ; field.
by apply INR_fact_neq_0.
eapply is_derive_ext.
intros t.
apply sym_equal, is_derive_n_unique, IH.
eapply le_trans, Hip ; by apply le_n_Sn.
evar_last.
apply is_derive_scal, is_derive_pow, is_derive_id.
rewrite MyNat.sub_succ_r.
change one with 1.
rewrite {1 2} (S_pred (p - i) O) /fact -/fact ?mult_INR.
field.
split.
apply INR_fact_neq_0.
apply not_0_INR, sym_not_eq, O_S.
by apply lt_minus_O_lt.

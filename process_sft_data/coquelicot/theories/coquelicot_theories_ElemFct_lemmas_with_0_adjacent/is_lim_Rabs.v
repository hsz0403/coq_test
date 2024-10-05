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

Lemma is_lim_Rabs (f : R -> R) (x l : Rbar) : is_lim f x l -> is_lim (fun x => Rabs (f x)) x (Rbar_abs l).
Proof.
destruct l as [l| | ] ; simpl ; intros ; first last.
eapply is_lim_comp.
2: by apply H.
by apply filterlim_Rabs.
destruct x ; by exists (mkposreal _ Rlt_0_1).
eapply is_lim_comp.
2: by apply H.
by apply filterlim_Rabs.
destruct x ; by exists (mkposreal _ Rlt_0_1).
apply is_lim_comp_continuous => //.
by apply continuous_Rabs.

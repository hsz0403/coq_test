Require Import Reals Omega Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.
Require Import Lim_seq Rbar Hierarchy.
Section Definitions.
Context {K : AbsRing} {V : NormedModule K}.
Definition is_series (a : nat -> V) (l : V) := filterlim (sum_n a) (eventually) (locally l).
Definition ex_series (a : nat -> V) := exists l : V, is_series a l.
Definition Cauchy_series (a : nat -> V) := forall eps : posreal, exists N : nat, forall n m : nat, (N <= n)%nat -> (N <= m)%nat -> norm (sum_n_m a n m) < eps.
End Definitions.
Definition Series (a : nat -> R) : R := real (Lim_seq (sum_n a)).
Section Properties1.
Context {K : AbsRing} {V : NormedModule K}.
End Properties1.
Section Properties2.
Context {K : AbsRing} {V : NormedModule K}.
End Properties2.
Section Properties3.
Context {K : AbsRing} {V : NormedModule K}.
End Properties3.

Lemma is_series_incr_1 (a : nat -> V) (l : V) : is_series a (plus l (a O)) -> is_series (fun k => a (S k)%nat) l.
Proof.
intros H.
apply filterlim_ext with (fun k => plus (sum_n a (S k)) (opp (a 0%nat))).
induction x; simpl.
rewrite sum_Sn !sum_O (plus_comm _ (a 1%nat)); rewrite <- plus_assoc.
now rewrite plus_opp_r plus_zero_r.
rewrite !sum_Sn -IHx -!sum_Sn sum_Sn; simpl.
rewrite <- plus_assoc, <- (plus_assoc _ _ (a (S (S x)))).
apply f_equal; apply plus_comm.
apply filterlim_comp with (G:=(locally (plus l (a 0%nat)))) (g:=fun x => plus x (opp (a 0%nat))).
apply filterlim_comp with (f:= fun x => S x) (2:=H).
apply eventually_subseq; intros n; omega.
pattern l at 2; replace l with (plus (plus l (a 0%nat)) (opp (a 0%nat))).
apply filterlim_comp_2 with (3 := filterlim_plus _ _).
apply filterlim_id.
apply filterlim_const.
rewrite <- plus_assoc, plus_opp_r.
apply plus_zero_r.

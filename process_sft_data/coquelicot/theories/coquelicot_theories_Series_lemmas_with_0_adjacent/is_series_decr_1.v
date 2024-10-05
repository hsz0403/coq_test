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

Lemma is_series_decr_1 (a : nat -> V) (l : V) : is_series (fun k => a (S k)%nat) (plus l (opp (a O))) -> is_series a l.
Proof.
intros H.
apply filterlim_ext_loc with (fun v => plus (a 0%nat) (sum_n (fun k : nat => a (S k)) (pred v))).
exists 1%nat.
intros n Hn; apply sym_eq.
rewrite /sum_n sum_Sn_m.
apply f_equal.
rewrite sum_n_m_S.
apply f_equal ; omega.
by apply le_O_n.
replace l with (plus (a 0%nat) (plus l (opp (a 0%nat)))).
apply filterlim_comp_2 with (3 := filterlim_plus _ _).
apply filterlim_id.
apply filterlim_const.
apply filterlim_comp with (f:= fun x => pred x) (2:=H).
intros P (N1,HN1).
exists (S N1).
intros n Hn; apply HN1; omega.
rewrite plus_comm; rewrite <- plus_assoc.
rewrite (plus_comm _ (a 0%nat)); rewrite plus_opp_r.
apply plus_zero_r.

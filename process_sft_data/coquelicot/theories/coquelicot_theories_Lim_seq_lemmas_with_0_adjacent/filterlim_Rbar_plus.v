Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.
Require Import Rbar Lub Markov Hierarchy.
Open Scope R_scope.
Definition is_sup_seq (u : nat -> Rbar) (l : Rbar) := match l with | Finite l => forall (eps : posreal), (forall n, Rbar_lt (u n) (l+eps)) /\ (exists n, Rbar_lt (l-eps) (u n)) | p_infty => forall M : R, exists n, Rbar_lt M (u n) | m_infty => forall M : R, forall n, Rbar_lt (u n) M end.
Definition is_inf_seq (u : nat -> Rbar) (l : Rbar) := match l with | Finite l => forall (eps : posreal), (forall n, Rbar_lt (Finite (l-eps)) (u n)) /\ (exists n, Rbar_lt (u n) (Finite (l+eps))) | p_infty => forall M : R, forall n, Rbar_lt (Finite M) (u n) | m_infty => forall M : R, exists n, Rbar_lt (u n) (Finite M) end.
Definition Sup_seq (u : nat -> Rbar) := proj1_sig (ex_sup_seq u).
Definition Inf_seq (u : nat -> Rbar) := proj1_sig (ex_inf_seq u).
Definition is_LimSup_seq (u : nat -> R) (l : Rbar) := match l with | Finite l => forall eps : posreal, (forall N : nat, exists n : nat, (N <= n)%nat /\ l - eps < u n) /\ (exists N : nat, forall n : nat, (N <= n)%nat -> u n < l + eps) | p_infty => forall M : R, (forall N : nat, exists n : nat, (N <= n)%nat /\ M < u n) | m_infty => forall M : R, (exists N : nat, forall n : nat, (N <= n)%nat -> u n < M) end.
Definition is_LimInf_seq (u : nat -> R) (l : Rbar) := match l with | Finite l => forall eps : posreal, (forall N : nat, exists n : nat, (N <= n)%nat /\ u n < l + eps) /\ (exists N : nat, forall n : nat, (N <= n)%nat -> l - eps < u n) | p_infty => forall M : R, (exists N : nat, forall n : nat, (N <= n)%nat -> M < u n) | m_infty => forall M : R, (forall N : nat, exists n : nat, (N <= n)%nat /\ u n < M) end.
Definition LimSup_seq (u : nat -> R) := proj1_sig (ex_LimSup_seq u).
Definition LimInf_seq (u : nat -> R) := proj1_sig (ex_LimInf_seq u).
Definition is_lim_seq (u : nat -> R) (l : Rbar) := filterlim u eventually (Rbar_locally l).
Definition is_lim_seq' (u : nat -> R) (l : Rbar) := match l with | Finite l => forall eps : posreal, eventually (fun n => Rabs (u n - l) < eps) | p_infty => forall M : R, eventually (fun n => M < u n) | m_infty => forall M : R, eventually (fun n => u n < M) end.
Definition ex_lim_seq (u : nat -> R) := exists l, is_lim_seq u l.
Definition ex_finite_lim_seq (u : nat -> R) := exists l : R, is_lim_seq u l.
Definition Lim_seq (u : nat -> R) : Rbar := Rbar_div_pos (Rbar_plus (LimSup_seq u) (LimInf_seq u)) {| pos := 2; cond_pos := Rlt_R0_R2 |}.
Definition ex_lim_seq_cauchy (u : nat -> R) := forall eps : posreal, exists N : nat, forall n m, (N <= n)%nat -> (N <= m)%nat -> Rabs (u n - u m) < eps.

Lemma filterlim_Rbar_plus : forall x y z, is_Rbar_plus x y z -> filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally x) (Rbar_locally y)) (Rbar_locally z).
Proof.
intros x y z.
wlog: x y z / (Rbar_le 0 z).
intros Hw.
case: (Rbar_le_lt_dec 0 z) => Hz Hp.
by apply Hw.
apply (filterlim_ext (fun z => - (- fst z + - snd z))).
intros t.
ring.
rewrite -(Rbar_opp_involutive z).
eapply filterlim_comp.
2: apply filterlim_Rbar_opp.
assert (Hw' : filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally (Rbar_opp x)) (Rbar_locally (Rbar_opp y))) (Rbar_locally (Rbar_opp z))).
apply Hw.
rewrite -Ropp_0 -/(Rbar_opp 0).
apply <- Rbar_opp_le.
now apply Rbar_lt_le.
revert Hp.
clear.
destruct x as [x| |] ; destruct y as [y| |] ; destruct z as [z| |] => //=.
unfold is_Rbar_plus ; simpl => H.
injection H => <-.
apply f_equal, f_equal ; ring.
clear Hw.
intros P HP.
specialize (Hw' P HP).
destruct Hw' as [Q R H1 H2 H3].
exists (fun x => Q (- x)) (fun x => R (- x)).
now apply filterlim_Rbar_opp.
now apply filterlim_Rbar_opp.
intros u v HQ HR.
exact (H3 _ _ HQ HR).
unfold is_Rbar_plus.
case: z => [z| |] Hz Hp ; try by case: Hz.
case: x y Hp Hz => [x| |] ; case => [y| |] //= ; case => <- Hz.
intros P [eps He].
exists (fun u => Rabs (u - x) < pos_div_2 eps) (fun v => Rabs (v - y) < pos_div_2 eps).
now exists (pos_div_2 eps).
now exists (pos_div_2 eps).
intros u v Hu Hv.
apply He.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
replace (u + v + - (x + y)) with ((u - x) + (v - y)) by ring.
rewrite (double_var eps) ; apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
now apply Hu.
now apply Hv.
wlog: x y Hp {Hz} / (is_finite x) => [Hw|Hx].
case: x y Hp {Hz} => [x| |] ; case => [y| |] // _.
now apply (Hw x p_infty).
assert (Hw': filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally y) (Rbar_locally p_infty)) (Rbar_locally p_infty)).
exact: Hw.
intros P HP.
specialize (Hw' P HP).
destruct Hw' as [Q R H1 H2 H3].
exists R Q ; try assumption.
intros u v Hu Hv.
rewrite Rplus_comm.
now apply (H3 v u).
clear Hw.
intros P [N HN].
exists (fun x => N/2 < x) (fun x => N/2 < x).
now exists (N/2).
now exists (N/2).
intros x y Hx Hy.
simpl.
apply HN.
rewrite (double_var N).
now apply Rplus_lt_compat.
case: x y Hp Hx => [x| |] ; case => [y| | ] //= _ _.
intros P [N HN].
exists (fun u => Rabs (u - x) < 1) (fun v => N - x + 1 < v).
now exists (mkposreal _ Rlt_0_1).
now exists (N - x + 1).
intros u v Hu Hv.
simpl.
apply HN.
replace N with (x - 1 + (N - x + 1)) by ring.
apply Rplus_lt_compat.
now apply Rabs_lt_between'.
exact Hv.

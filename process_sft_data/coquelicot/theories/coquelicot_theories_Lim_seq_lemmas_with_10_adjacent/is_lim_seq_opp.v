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

Lemma is_lim_seq_le_le (u v w : nat -> R) (l : Rbar) : (forall n, u n <= v n <= w n) -> is_lim_seq u l -> is_lim_seq w l -> is_lim_seq v l.
Proof.
intros H.
apply filterlim_le_le.
Admitted.

Lemma is_lim_seq_le_p_loc (u v : nat -> R) : eventually (fun n => u n <= v n) -> is_lim_seq u p_infty -> is_lim_seq v p_infty.
Proof.
Admitted.

Lemma is_lim_seq_le_m_loc (u v : nat -> R) : eventually (fun n => v n <= u n) -> is_lim_seq u m_infty -> is_lim_seq v m_infty.
Proof.
Admitted.

Lemma is_lim_seq_decr_compare (u : nat -> R) (l : R) : is_lim_seq u l -> (forall n, (u (S n)) <= (u n)) -> forall n, l <= u n.
Proof.
move /is_lim_seq_spec => Hu H n.
apply Rnot_lt_le => H0.
apply Rminus_lt_0 in H0.
case: (Hu (mkposreal _ H0)) => {Hu} /= Nu Hu.
move: (Hu _ (le_plus_r n Nu)).
apply Rle_not_lt.
apply Rle_trans with (2 := Rabs_maj2 _).
rewrite Ropp_minus_distr'.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
elim: (Nu) => [ | m IH].
rewrite plus_0_r ; by apply Rle_refl.
rewrite -plus_n_Sm.
apply Rle_trans with (2 := IH).
Admitted.

Lemma is_lim_seq_incr_compare (u : nat -> R) (l : R) : is_lim_seq u l -> (forall n, (u n) <= (u (S n))) -> forall n, u n <= l.
Proof.
move /is_lim_seq_spec => Hu H n.
apply Rnot_lt_le => H0.
apply Rminus_lt_0 in H0.
case: (Hu (mkposreal _ H0)) => {Hu} /= Nu Hu.
move: (Hu _ (le_plus_r n Nu)).
apply Rle_not_lt.
apply Rle_trans with (2 := Rle_abs _).
apply Rplus_le_compat_r.
elim: (Nu) => [ | m IH].
rewrite plus_0_r ; by apply Rle_refl.
rewrite -plus_n_Sm.
apply Rle_trans with (1 := IH).
Admitted.

Lemma ex_lim_seq_decr (u : nat -> R) : (forall n, (u (S n)) <= (u n)) -> ex_lim_seq u.
Proof.
move => H.
exists (Inf_seq u).
apply is_lim_seq_spec.
rewrite /Inf_seq ; case: ex_inf_seq ; case => [l | | ] //= Hl.
move => eps ; case: (Hl eps) => Hl1 [N Hl2].
exists N => n Hn.
apply Rabs_lt_between' ; split.
by apply Hl1.
apply Rle_lt_trans with (2 := Hl2).
elim: n N {Hl2} Hn => [ | n IH] N Hn.
rewrite (le_n_O_eq _ Hn).
apply Rle_refl.
apply le_lt_eq_dec in Hn.
case: Hn => [Hn | ->].
apply Rle_trans with (1 := H _), IH ; intuition.
by apply Rle_refl.
move => M ; exists O => n _ ; by apply Hl.
move => M.
case: (Hl M) => {Hl} N Hl.
exists N => n Hn.
apply Rle_lt_trans with (2 := Hl).
elim: Hn => [ | {n} n Hn IH].
by apply Rle_refl.
apply Rle_trans with (2 := IH).
Admitted.

Lemma ex_lim_seq_incr (u : nat -> R) : (forall n, (u n) <= (u (S n))) -> ex_lim_seq u.
Proof.
move => H.
exists (Sup_seq u).
apply is_lim_seq_spec.
rewrite /Sup_seq ; case: ex_sup_seq ; case => [l | | ] //= Hl.
move => eps ; case: (Hl eps) => Hl1 [N Hl2].
exists N => n Hn.
apply Rabs_lt_between' ; split.
apply Rlt_le_trans with (1 := Hl2).
elim: Hn => [ | {n} n Hn IH].
by apply Rle_refl.
apply Rle_trans with (1 := IH).
by apply H.
by apply Hl1.
move => M.
case: (Hl M) => {Hl} N Hl.
exists N => n Hn.
apply Rlt_le_trans with (1 := Hl).
elim: Hn => [ | {n} n Hn IH].
by apply Rle_refl.
apply Rle_trans with (1 := IH).
by apply H.
Admitted.

Lemma ex_finite_lim_seq_decr (u : nat -> R) (M : R) : (forall n, (u (S n)) <= (u n)) -> (forall n, M <= u n) -> ex_finite_lim_seq u.
Proof.
intros.
apply ex_finite_lim_seq_correct.
have H1 : ex_lim_seq u.
exists (real (Inf_seq u)).
apply is_lim_seq_spec.
rewrite /Inf_seq ; case: ex_inf_seq ; case => [l | | ] //= Hl.
move => eps ; case: (Hl eps) => Hl1 [N Hl2].
exists N => n Hn.
apply Rabs_lt_between' ; split.
by apply Hl1.
apply Rle_lt_trans with (2 := Hl2).
elim: n N {Hl2} Hn => [ | n IH] N Hn.
rewrite (le_n_O_eq _ Hn).
apply Rle_refl.
apply le_lt_eq_dec in Hn.
case: Hn => [Hn | ->].
apply Rle_trans with (1 := H _), IH ; intuition.
by apply Rle_refl.
move: (Hl (u O) O) => H1 ; by apply Rlt_irrefl in H1.
case: (Hl M) => {Hl} n Hl.
apply Rlt_not_le in Hl.
by move: (Hl (H0 n)).
split => //.
apply Lim_seq_correct in H1.
case: (Lim_seq u) H1 => [l | | ] /= Hu.
by [].
apply is_lim_seq_spec in Hu.
case: (Hu (u O)) => {Hu} N Hu.
move: (Hu N (le_refl _)) => {Hu} Hu.
contradict Hu ; apply Rle_not_lt.
elim: N => [ | N IH].
by apply Rle_refl.
by apply Rle_trans with (1 := H _).
apply is_lim_seq_spec in Hu.
case: (Hu M) => {Hu} N Hu.
move: (Hu N (le_refl _)) => {Hu} Hu.
Admitted.

Lemma ex_finite_lim_seq_incr (u : nat -> R) (M : R) : (forall n, (u n) <= (u (S n))) -> (forall n, u n <= M) -> ex_finite_lim_seq u.
Proof.
intros.
case: (ex_finite_lim_seq_decr (fun n => - u n) (- M)).
move => n ; by apply Ropp_le_contravar.
move => n ; by apply Ropp_le_contravar.
move => l ; move => Hu.
exists (- l).
apply is_lim_seq_spec in Hu.
apply is_lim_seq_spec.
intros eps.
case: (Hu eps) => {Hu} N Hu.
exists N => n Hn.
replace (u n - - l) with (-(- u n - l)) by ring.
Admitted.

Lemma filterlim_Rbar_opp : forall x, filterlim Ropp (Rbar_locally x) (Rbar_locally (Rbar_opp x)).
Proof.
intros [x| |] P [eps He].
-
exists eps.
intros y Hy.
apply He.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
by rewrite Ropp_involutive Rplus_comm Rabs_minus_sym.
-
exists (-eps).
intros y Hy.
apply He.
apply Ropp_lt_cancel.
by rewrite Ropp_involutive.
-
exists (-eps).
intros y Hy.
apply He.
apply Ropp_lt_cancel.
Admitted.

Lemma ex_lim_seq_opp (u : nat -> R) : ex_lim_seq u <-> ex_lim_seq (fun n => -u n).
Proof.
split ; case => l Hl ; exists (Rbar_opp l).
by apply -> is_lim_seq_opp.
apply is_lim_seq_ext with (fun n => - - u n).
move => n ; by apply Ropp_involutive.
Admitted.

Lemma Lim_seq_opp (u : nat -> R) : Lim_seq (fun n => - u n) = Rbar_opp (Lim_seq u).
Proof.
rewrite /Lim_seq.
rewrite LimSup_seq_opp LimInf_seq_opp.
Admitted.

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
Admitted.

Lemma is_lim_seq_plus (u v : nat -> R) (l1 l2 l : Rbar) : is_lim_seq u l1 -> is_lim_seq v l2 -> is_Rbar_plus l1 l2 l -> is_lim_seq (fun n => u n + v n) l.
Proof.
intros Hu Hv Hl.
eapply filterlim_comp_2 ; try eassumption.
Admitted.

Lemma is_lim_seq_plus' (u v : nat -> R) (l1 l2 : R) : is_lim_seq u l1 -> is_lim_seq v l2 -> is_lim_seq (fun n => u n + v n) (l1 + l2).
Proof.
intros Hu Hv.
eapply is_lim_seq_plus.
by apply Hu.
by apply Hv.
Admitted.

Lemma ex_lim_seq_plus (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> ex_Rbar_plus (Lim_seq u) (Lim_seq v) -> ex_lim_seq (fun n => u n + v n).
Proof.
intros [lu Hu] [lv Hv] Hl ; exists (Rbar_plus lu lv).
apply is_lim_seq_plus with lu lv ; try assumption.
rewrite -(is_lim_seq_unique u lu) //.
rewrite -(is_lim_seq_unique v lv) //.
Admitted.

Lemma Lim_seq_plus (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> ex_Rbar_plus (Lim_seq u) (Lim_seq v) -> Lim_seq (fun n => u n + v n) = Rbar_plus (Lim_seq u) (Lim_seq v).
Proof.
intros Hu Hv Hl.
apply is_lim_seq_unique.
eapply is_lim_seq_plus ; try apply Lim_seq_correct ; try assumption.
Admitted.

Lemma is_lim_seq_minus (u v : nat -> R) (l1 l2 l : Rbar) : is_lim_seq u l1 -> is_lim_seq v l2 -> is_Rbar_minus l1 l2 l -> is_lim_seq (fun n => u n - v n) l.
Proof.
intros H1 H2 Hl.
eapply is_lim_seq_plus ; try eassumption.
Admitted.

Lemma is_lim_seq_minus' (u v : nat -> R) (l1 l2 : R) : is_lim_seq u l1 -> is_lim_seq v l2 -> is_lim_seq (fun n => u n - v n) (l1 - l2).
Proof.
intros Hu Hv.
eapply is_lim_seq_minus ; try eassumption.
Admitted.

Lemma ex_lim_seq_minus (u v : nat -> R) : ex_lim_seq u -> ex_lim_seq v -> ex_Rbar_minus (Lim_seq u) (Lim_seq v) -> ex_lim_seq (fun n => u n - v n).
Proof.
intros [lu Hu] [lv Hv] Hl ; exists (Rbar_minus lu lv).
eapply is_lim_seq_minus ; try eassumption.
rewrite -(is_lim_seq_unique u lu) //.
rewrite -(is_lim_seq_unique v lv) //.
Admitted.

Lemma is_lim_seq_opp (u : nat -> R) (l : Rbar) : is_lim_seq u l <-> is_lim_seq (fun n => -u n) (Rbar_opp l).
Proof.
split ; move => Hu.
apply is_LimSup_LimInf_lim_seq.
apply is_LimSup_opp_LimInf_seq.
by apply is_lim_LimInf_seq.
apply is_LimInf_opp_LimSup_seq.
by apply is_lim_LimSup_seq.
apply is_LimSup_LimInf_lim_seq.
apply is_LimInf_opp_LimSup_seq.
by apply is_lim_LimInf_seq.
apply is_LimSup_opp_LimInf_seq.
by apply is_lim_LimSup_seq.

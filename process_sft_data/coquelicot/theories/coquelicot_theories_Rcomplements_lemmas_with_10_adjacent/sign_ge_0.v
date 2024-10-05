Ltac evar_last := match goal with | |- ?f ?x => let tx := type of x in let tx := eval simpl in tx in let tmp := fresh "tmp" in evar (tmp : tx) ; refine (@eq_ind tx tmp f _ x _) ; unfold tmp ; clear tmp end.
Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Module MyNat.
End MyNat.
Require Import Even Div2.
Require Import mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool.
Open Scope R_scope.
Definition floor x := proj1_sig (floor_ex x).
Definition floor1 x := proj1_sig (floor1_ex x).
Definition nfloor x pr := proj1_sig (nfloor_ex x pr).
Definition nfloor1 x pr := proj1_sig (nfloor1_ex x pr).
Fixpoint pow2 (n : nat) : nat := match n with | O => 1%nat | S n => (2 * pow2 n)%nat end.
Definition pos_div_2 (eps : posreal) := mkposreal _ (is_pos_div_2 eps).
Definition sign (x : R) := match total_order_T 0 x with | inleft (left _) => 1 | inleft (right _) => 0 | inright _ => -1 end.
Definition belast {T : Type} (s : seq T) := match s with | [::] => [::] | h :: s => belast h s end.

Lemma Rabs_lt_between_Rmax : forall x m M, m < x < M -> Rabs x < Rmax M (-m).
Proof.
intros x m M Hx.
unfold Rabs ; destruct Rcase_abs as [H|H].
apply Rlt_le_trans with (2 := RmaxLess2 _ _).
apply Ropp_lt_contravar, Hx.
apply Rlt_le_trans with (2 := RmaxLess1 _ _).
Admitted.

Lemma Rabs_maj2 : forall x, -x <= Rabs x.
Proof.
intros.
rewrite <- Rabs_Ropp.
Admitted.

Lemma Req_lt_aux : forall x y, (forall eps : posreal, Rabs (x - y) < eps) -> x = y.
Proof.
intros.
apply Rminus_diag_uniq.
apply Rabs_eq_0.
apply Rle_antisym.
apply le_epsilon.
intros.
rewrite Rplus_0_l.
apply Rlt_le.
apply (H (mkposreal eps H0)).
Admitted.

Lemma Req_le_aux : forall x y, (forall eps : posreal, Rabs (x - y) <= eps) -> x = y.
Proof.
intros.
apply Rminus_diag_uniq.
apply Rabs_eq_0.
apply Rle_antisym.
apply le_epsilon.
intros.
rewrite Rplus_0_l.
apply (H (mkposreal eps H0)).
Admitted.

Lemma is_pos_div_2 (eps : posreal) : 0 < eps / 2.
Proof.
Admitted.

Lemma sign_0 : sign 0 = 0.
Proof.
unfold sign.
case total_order_T as [[H|H]|H].
elim (Rlt_irrefl _ H).
exact H.
Admitted.

Lemma sign_opp (x : R) : sign (-x) = - sign x.
Proof.
unfold sign.
Admitted.

Lemma sign_eq_1 (x : R) : 0 < x -> sign x = 1.
Proof.
intros Hx.
unfold sign.
Admitted.

Lemma sign_eq_m1 (x : R) : x < 0 -> sign x = -1.
Proof.
intros Hx.
unfold sign.
Admitted.

Lemma sign_le (x y : R) : x <= y -> sign x <= sign y.
Proof.
intros Hx.
unfold sign.
Admitted.

Lemma sign_le_0 (x : R) : x <= 0 -> sign x <= 0.
Proof.
intros Hx.
rewrite <- sign_0.
Admitted.

Lemma sign_neq_0 (x : R) : x <> 0 -> sign x <> 0.
Proof.
intros Hx.
unfold sign.
Admitted.

Lemma sign_mult (x y : R) : sign (x * y) = sign x * sign y.
Proof.
wlog: x / (0 < x) => [Hw | Hx].
case: (Rle_lt_dec 0 x) => Hx.
case: Hx => Hx.
by apply Hw.
rewrite -Hx Rmult_0_l.
rewrite sign_0.
by rewrite Rmult_0_l.
rewrite -(Ropp_involutive x).
rewrite sign_opp Ropp_mult_distr_l_reverse sign_opp Hw.
ring.
by apply Ropp_0_gt_lt_contravar.
wlog: y / (0 < y) => [Hw | Hy].
case: (Rle_lt_dec 0 y) => Hy.
case: Hy => Hy.
by apply Hw.
rewrite -Hy Rmult_0_r.
rewrite sign_0.
by rewrite Rmult_0_r.
rewrite -(Ropp_involutive y).
rewrite sign_opp Ropp_mult_distr_r_reverse sign_opp Hw.
ring.
by apply Ropp_0_gt_lt_contravar.
have Hxy : 0 < x * y.
by apply Rmult_lt_0_compat.
rewrite -> 3!sign_eq_1 by easy.
Admitted.

Lemma sign_min_max (a b : R) : sign (b - a) * (Rmax a b - Rmin a b) = b - a.
Proof.
unfold sign.
case total_order_T as [[H|H]|H].
assert (K := proj2 (Rminus_le_0 a b) (Rlt_le _ _ H)).
rewrite (Rmax_right _ _ K) (Rmin_left _ _ K).
apply Rmult_1_l.
rewrite -H.
apply Rmult_0_l.
assert (K : b <= a).
apply Rnot_lt_le.
contradict H.
apply Rle_not_lt.
apply -> Rminus_le_0.
now apply Rlt_le.
rewrite (Rmax_left _ _ K) (Rmin_right _ _ K).
Admitted.

Lemma sum_INR : forall n, sum_f_R0 INR n = INR n * (INR n + 1) / 2.
Proof.
elim => [ | n IH] ; rewrite /sum_f_R0 -/sum_f_R0 ?S_INR /=.
rewrite /Rdiv ; ring.
Admitted.

Lemma interval_finite_subdiv (a b : R) (eps : posreal) : (a <= b) -> {l : seq R | head 0 l = a /\ last 0 l = b /\ forall i, (S i < size l)%nat -> nth 0 l i < nth 0 l (S i) <= nth 0 l i + eps}.
Proof.
move => Hab.
suff Hn : 0 <= (b - a) / eps.
set n : nat := nfloor ((b - a) / eps) Hn.
case: (Req_EM_T (INR n) ((b - a) / eps)) => Hdec.
set l : seq R := mkseq (fun k => a + INR k * eps) (S n).
exists l.
split.
simpl ; rewrite /Rdiv ; ring.
split.
replace b with (a + INR n * eps).
simpl.
rewrite (last_map (fun k => a + INR k * eps) _ O) /=.
rewrite (last_nth O) size_iota /=.
case H : n => [ | m].
by simpl.
by rewrite /nth -/(nth _ _ m) nth_iota.
rewrite Hdec ; field.
by apply Rgt_not_eq, eps.
move => i Hi ; rewrite size_mkseq in Hi.
split.
rewrite ?nth_mkseq //.
rewrite S_INR Rminus_lt_0 ; ring_simplify.
by apply eps.
elim: (S n) (S i) Hi => /= [ | m IH] ; case => /= [ | j] Hj //.
by apply lt_irrefl in Hj.
by apply lt_n_O in Hj.
by apply IH, lt_S_n.
elim: (S n) (S i) Hi => /= [ | m IH] ; case => /= [ | j] Hj //.
by apply lt_n_O in Hj.
by apply IH, lt_S_n.
rewrite ?nth_mkseq //.
rewrite S_INR Rminus_le_0 ; ring_simplify.
by apply Rle_refl.
elim: (S n) (S i) Hi => /= [ | m IH] ; case => /= [ | j] Hj //.
by apply lt_n_O in Hj.
by apply IH, lt_S_n.
elim: (S n) (S i) Hi => /= [ | m IH] ; case => /= [ | j] Hj //.
by apply lt_n_O in Hj.
by apply lt_n_O in Hj.
by apply IH, lt_S_n.
set l : seq R := rcons (mkseq (fun k => a + INR k * eps) (S n)) b.
exists l.
split.
simpl ; rewrite /Rdiv ; ring.
split.
simpl ; by rewrite last_rcons.
move => i Hi ; rewrite size_rcons size_mkseq in Hi ; apply lt_n_Sm_le, le_S_n in Hi.
split.
rewrite ?nth_rcons size_mkseq.
have H : ssrnat.leq (S i) (S n) = true.
apply le_n_S in Hi ; elim: (S i) (S n) Hi => //= j IH ; case => //= [ | m] Hi.
by apply le_Sn_O in Hi.
apply IH ; by apply le_S_n.
case: (ssrnat.leq (S i) (S n)) (H) => // _.
case H0 : (ssrnat.leq (S (S i)) (S n)) => //.
rewrite ?nth_mkseq //.
rewrite S_INR Rminus_lt_0 ; ring_simplify.
by apply eps.
apply (f_equal negb) in H0 ; simpl in H0.
rewrite -ssrnat.leqNgt in H0.
case H1 : (@eqtype.eq_op ssrnat.nat_eqType (S i) (S n)) => //.
rewrite ssrnat.eqSS /= in H1.
replace i with n.
rewrite nth_mkseq => //.
move: Hdec ; rewrite /n /nfloor.
case: nfloor_ex => {n Hn l Hi H H0 H1} n Hn /= Hdec.
rewrite Rplus_comm ; apply Rlt_minus_r.
apply Rlt_div_r.
by apply eps.
case: Hn => Hn _ ; case: Hn => // Hn.
elim: n i H1 {Hi H H0 l Hdec} => [ | n IH] ; case => [ | i] // H.
apply f_equal, IH ; intuition.
by rewrite ssrnat.eqn_leq H H0 in H1.
rewrite ?nth_rcons size_mkseq.
have H : ssrnat.leq (S i) (S n) = true.
apply le_n_S in Hi ; elim: (S i) (S n) Hi => //= j IH ; case => //= [ | m] Hi.
by apply le_Sn_O in Hi.
apply IH ; by apply le_S_n.
case: (ssrnat.leq (S i) (S n)) (H) => // _.
case H0 : (ssrnat.leq (S (S i)) (S n)) => //.
rewrite ?nth_mkseq //.
rewrite S_INR Rminus_le_0 ; ring_simplify.
by apply Rle_refl.
apply (f_equal negb) in H0 ; simpl in H0.
rewrite -ssrnat.leqNgt in H0.
case H1 : (@eqtype.eq_op ssrnat.nat_eqType (S i) (S n)) => //.
rewrite ssrnat.eqSS /= in H1.
replace i with n.
rewrite nth_mkseq => //.
move: Hdec ; rewrite /n /nfloor.
case: nfloor_ex => {n Hn l Hi H H0 H1} n Hn /= Hdec.
rewrite Rplus_assoc Rplus_comm ; apply Rle_minus_l.
replace (INR n * eps + eps) with ((INR n + 1) * eps) by ring.
apply Rle_div_l.
by apply eps.
by apply Rlt_le, Hn.
elim: n i H1 {Hi H H0 l Hdec} => [ | n IH] ; case => [ | i] // H.
apply f_equal, IH ; intuition.
by rewrite ssrnat.eqn_leq H H0 in H1.
apply Rdiv_le_0_compat.
by apply Rminus_le_0 in Hab.
Admitted.

Lemma interval_finite_subdiv_between (a b : R) (eps : posreal) (Hab : a <= b) : let l := proj1_sig (interval_finite_subdiv a b eps Hab) in forall i, (i < size l)%nat -> a <= nth 0 l i <= b.
Proof.
case: interval_finite_subdiv => l Hl /= i Hi.
case: Hl => <- ; case => <- Hl.
move: (fun i Hi => proj1 (Hl i Hi)) => {Hl} Hl.
rewrite -nth0 (last_nth 0).
suff : forall n m, (n <= m)%nat -> (m < size l)%nat -> nth 0 l n <= nth 0 l m.
move => {Hl} Hl ; split.
apply Hl ; by intuition.
case: l Hi Hl => /= [ | x0 l] Hi Hl.
by apply lt_n_O in Hi.
apply Hl ; by intuition.
elim: l Hl {i Hi} => [ | x0 l IH] Hl n m Hnm Hm.
by apply lt_n_O in Hm.
case: n m Hnm Hm => [ | n] m //= Hnm Hm.
clear Hnm ; elim: m Hm => {IH} /= [ | m IH] Hm.
by apply Rle_refl.
apply Rle_trans with (nth 0 (x0 :: l) m).
apply IH ; intuition.
by apply Rlt_le, Hl.
case: m Hnm Hm => /= [ | m] Hnm Hm.
by apply le_Sn_O in Hnm.
apply IH ; try by intuition.
move => i Hi.
apply (Hl (S i)).
Admitted.

Lemma SSR_leq (n m : nat) : is_true (ssrnat.leq n m) <-> (n <= m)%nat.
Proof.
Admitted.

Lemma SSR_minus (n m : nat) : ssrnat.subn n m = (n - m)%nat.
Proof.
Admitted.

Lemma rcons_ind {T : Type} (P : seq T -> Type) : P [::] -> (forall (s : seq T) (t : T), P s -> P (rcons s t)) -> forall s, P s.
Proof.
move => H0 Hr s ; move: (refl_equal (size s)).
move: {1}(size s) => n ; elim: n s => // [| n IH] s Hn ; case: s Hn => [| h s] Hn //.
have: ({s0 : _&{ t0 | h::s = rcons s0 t0}}) ; [| case => s0 [t0 H]].
elim: (s) (h) => {s h Hn IH} [| h s IH] h0.
exists [::] ; by exists h0.
case: (IH h) => s0 [t0 H] ; exists (h0::s0) ; exists t0 ; by rewrite rcons_cons -H.
Admitted.

Lemma sign_ge_0 (x : R) : 0 <= x -> 0 <= sign x.
Proof.
intros Hx.
rewrite <- sign_0.
now apply sign_le.

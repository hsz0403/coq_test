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
by apply eps.

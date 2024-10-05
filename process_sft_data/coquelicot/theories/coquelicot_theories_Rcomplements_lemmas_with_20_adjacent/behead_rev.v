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

Lemma sign_ge_0 (x : R) : 0 <= x -> 0 <= sign x.
Proof.
intros Hx.
rewrite <- sign_0.
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

Lemma rcons_dec {T : Type} (P : seq T -> Type) : (P [::]) -> (forall s t, P (rcons s t)) -> forall s, P s.
Proof.
move => H0 Hr ; case => [| h s] //.
have: ({s0 : _&{ t0 | h::s = rcons s0 t0}}) ; [| case => s0 [t0 H]].
elim: s h => [| h s IH] h0.
exists [::] ; by exists h0.
case: (IH h) => s0 [t0 H] ; exists (h0::s0) ; exists t0 ; by rewrite rcons_cons -H.
Admitted.

Lemma size_rcons_pos {T : Type} (s : seq T) (t : T) : (0 < size (rcons s t))%nat.
Proof.
Admitted.

Lemma foldr_rcons {T T0 : Type} : forall (f : T0 -> T -> T) x0 s t, foldr f x0 (rcons s t) = foldr f (f t x0) s.
Proof.
Admitted.

Lemma foldl_rcons {T T0 : Type} : forall (f : T -> T0 -> T) x0 s t, foldl f x0 (rcons s t) = f (foldl f x0 s) t.
Proof.
Admitted.

Lemma head_rcons {T : Type} (x0 : T) (s : seq T) (t : T) : head x0 (rcons s t) = head t s.
Proof.
Admitted.

Lemma behead_rcons {T : Type} (s : seq T) (t : T) : (0 < size s)%nat -> behead (rcons s t) = rcons (behead s) t.
Proof.
Admitted.

Lemma pairmap_rcons {T T0 : Type} (f : T -> T -> T0) (s : seq T) h0 h x0 : pairmap f x0 (rcons (rcons s h0) h) = rcons (pairmap f x0 (rcons s h0)) (f h0 h).
Proof.
Admitted.

Lemma map_pairmap {T T0 T1 : Type} (f : T0 -> T1) (g : T -> T -> T0) (s : seq T) (x0 : T) : map f (pairmap g x0 s) = pairmap (fun x y => f (g x y)) x0 s.
Proof.
elim: s x0 => [| h s IH] x0 //=.
Admitted.

Lemma pairmap_map {T T0 T1 : Type} (f : T0 -> T0 -> T1) (g : T -> T0) (s : seq T) (x0 : T) : pairmap f (g x0) (map g s) = pairmap (fun x y => f (g x) (g y)) x0 s.
Proof.
elim: s x0 => [| h s IH] x0 //=.
Admitted.

Lemma size_unzip1 {T T0 : Type} (s : seq (T * T0)) : size (unzip1 s) = size s.
Proof.
Admitted.

Lemma size_unzip2 {T T0 : Type} (s : seq (T * T0)) : size (unzip2 s) = size s.
Proof.
Admitted.

Lemma zip_cons {S T : Type} hs ht (s : seq S) (t : seq T) : zip (hs :: s) (ht :: t) = (hs,ht) :: zip s t.
Proof.
Admitted.

Lemma zip_rcons {S T : Type} (s : seq S) (t : seq T) hs ht : size s = size t -> zip (rcons s hs) (rcons t ht) = rcons (zip s t) (hs,ht).
Proof.
elim: s t hs ht => [| hs s IHs] ; case => //= ht t hs' ht' Hs.
Admitted.

Lemma unzip1_rcons {S T : Type} (s : seq (S*T)) (h : S*T) : unzip1 (rcons s h) = rcons (unzip1 s) (fst h).
Proof.
Admitted.

Lemma unzip2_rcons {S T : Type} (s : seq (S*T)) (h : S*T) : unzip2 (rcons s h) = rcons (unzip2 s) (snd h).
Proof.
Admitted.

Lemma unzip1_belast {S T : Type} (s : seq (S*T)) : unzip1 (belast s) = belast (unzip1 s).
Proof.
Admitted.

Lemma unzip2_belast {S T : Type} (s : seq (S*T)) : unzip2 (belast s) = belast (unzip2 s).
Proof.
Admitted.

Lemma unzip1_behead {S T : Type} (s : seq (S*T)) : unzip1 (behead s) = behead (unzip1 s).
Proof.
Admitted.

Lemma unzip2_behead {S T : Type} (s : seq (S*T)) : unzip2 (behead s) = behead (unzip2 s).
Proof.
Admitted.

Lemma unzip1_fst {S T : Type} (s : seq (S*T)) : unzip1 s = map (@fst S T) s.
Proof.
Admitted.

Lemma unzip2_snd {S T : Type} (s : seq (S*T)) : unzip2 s = map (@snd S T) s.
Proof.
Admitted.

Lemma size_belast' {T : Type} (s : seq T) : size (belast s) = Peano.pred (size s).
Proof.
case: s => /= [ | x0 s] //.
Admitted.

Lemma head_map {T1 T2 : Type} (f : T1 -> T2) (s : seq T1) (x : T1) : head (f x) (map f s) = f (head x s).
Proof.
Admitted.

Lemma StepFun_bound {a b : R} (f : StepFun a b) : exists s : R, forall x, Rmin a b <= x <= Rmax a b -> f x <= s.
Proof.
case: f => /= f [lx [ly [Hsort [Hhead [Hlast [Hsize Hval]]]]]]; rename a into a0 ; rename b into b0 ; set a := Rmin a0 b0 ; set b := Rmax a0 b0 ; set Rl_max := fun x0 => fix f l := match l with | RList.nil => x0 | RList.cons h t => Rmax h (f t) end ; set f_lx := (fix app l := match l with | RList.nil => RList.nil | RList.cons h t => RList.cons (f h) (app t) end) lx ; set M_f_lx := Rl_max (f 0) f_lx ; set M_ly := Rl_max 0 ly.
exists (Rmax M_f_lx M_ly) => x [Hx Hx'].
rewrite /M_f_lx /f_lx ; case: lx Hsort Hhead Hlast Hsize Hval {f_lx M_f_lx}.
move => _ _ _ H ; contradict H ; apply O_S.
move => h l ; case: l h.
move => h _ Ha Hb _ _ ; simpl in Ha, Hb.
rewrite /a -Ha in Hx ; rewrite /b -Hb in Hx'.
rewrite (Rle_antisym _ _ Hx Hx') /= ; apply Rle_trans with (2 := RmaxLess1 _ _) ; apply RmaxLess1.
move => h l h' Hsort Hhead Hlast Hsize Hval.
apply Rle_lt_or_eq_dec in Hx' ; case: Hx' => Hx'.
have H : exists i : nat, (i < S (Rlength l))%nat /\ (pos_Rl (RList.cons h' (RList.cons h l)) i) <= x < (pos_Rl (RList.cons h' (RList.cons h l)) (S i)).
rewrite /a -Hhead in Hx ; rewrite /b -Hlast in Hx'.
elim: l h' h Hx Hx' Hsort {Hhead Hlast Hsize Hval} => [| h'' l IH] h' h Hx Hx' Hsort ; simpl in Hx, Hsort.
case: (Rlt_le_dec x h) => H.
exists O ; intuition.
exists O => /= ; intuition.
case: (Rlt_le_dec x h) => H.
exists O => /= ; intuition.
have H0 : ordered_Rlist (RList.cons h (RList.cons h'' l)).
move => i Hi ; apply (Hsort (S i)) => /= ; apply lt_n_S, Hi.
case: (IH _ _ H Hx' H0) => {IH} i Hi.
exists (S i) ; split.
simpl ; apply lt_n_S, Hi => /=.
apply Hi.
case: H => i [Hi [Ht Ht']].
apply Rle_lt_or_eq_dec in Ht ; case: Ht => Ht.
rewrite (Hval i Hi x).
apply Rle_trans with (2 := RmaxLess2 _ _).
rewrite /M_ly ; case: (ly).
apply Rle_refl.
move => y ly' ; elim: ly' (i) y.
move => i0 y ; case: i0 => //=.
apply RmaxLess1.
move => _; apply RmaxLess2.
move => y ly' IH i0 y' ; case: i0.
apply RmaxLess1.
move => n ; apply Rle_trans with (1 := IH n y) ; apply RmaxLess2.
split => //.
rewrite -Ht ; apply Rle_trans with (2 := RmaxLess1 _ _).
case: (i).
apply RmaxLess1.
move => n ; elim: n (h) (h') (l).
move => h0 h'0 l0 ; apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess1.
move => n IH h0 h'0 l0.
case: l0.
apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess2.
move => h''0 l0 ; apply Rle_trans with (1 := IH h''0 h0 l0), RmaxLess2.
rewrite Hx' /b -Hlast.
apply Rle_trans with (2 := RmaxLess1 _ _).
elim: (l) (h') (h) => [| h''0 l0 IH] h'0 h0.
apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess1.
Admitted.

Lemma Riemann_integrable_bound (f : R -> R) (a b : R) : Riemann_integrable f a b -> exists s : R, forall x, Rmin a b <= x <= Rmax a b -> f x <= s.
Proof.
move => pr ; case (pr (mkposreal _ Rlt_0_1)) => {pr} phi [psi [pr _]] ; case: (StepFun_bound phi) => M_phi H_phi ; case: (StepFun_bound psi) => M_psi H_psi ; exists (M_psi + M_phi) => x Hx.
apply Rle_trans with (2 := Rplus_le_compat _ _ _ _ (H_psi _ Hx) (H_phi _ Hx)).
have: (f x = (f x - phi x) + phi x) ; first by ring.
Admitted.

Lemma Riemann_integrable_ext : forall (f g : R -> R) (a b : R), (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) -> Riemann_integrable f a b -> Riemann_integrable g a b.
Proof.
intros f g a b Heq pr_f.
intro eps.
elim (pr_f eps) ; clear pr_f ; intros phi (psi, pr_f).
exists phi.
exists psi.
split ; intros.
rewrite <- (Heq t H).
apply (proj1 pr_f t H).
Admitted.

Lemma behead_rev {T : Type} (s : seq T) : behead (rev s) = rev (belast s).
Proof.
case: s => // t s ; elim: s t => // t s IHs t0.
rewrite rev_cons behead_rcons ?IHs ?size_rev -?rev_cons //= ; by apply lt_0_Sn.

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

Lemma head_rcons {T : Type} (x0 : T) (s : seq T) (t : T) : head x0 (rcons s t) = head t s.
Proof.
Admitted.

Lemma behead_rcons {T : Type} (s : seq T) (t : T) : (0 < size s)%nat -> behead (rcons s t) = rcons (behead s) t.
Proof.
Admitted.

Lemma behead_rev {T : Type} (s : seq T) : behead (rev s) = rev (belast s).
Proof.
case: s => // t s ; elim: s t => // t s IHs t0.
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

Lemma RiemannInt_ext : forall (f g : R -> R) (a b : R) (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b) (Heq : forall x, Rmin a b <= x <= Rmax a b -> f x = g x), RiemannInt pr_f = RiemannInt pr_g.
Proof.
intros.
destruct (Rle_lt_dec a b).
apply RiemannInt_P18.
apply r.
intros.
apply Heq.
split.
rewrite (Rmin_left _ _ r).
apply Rlt_le ; apply H.
rewrite (Rmax_right _ _ r).
apply Rlt_le ; apply H.
rewrite (RiemannInt_P8 pr_f (RiemannInt_P1 pr_f)).
rewrite (RiemannInt_P8 pr_g (RiemannInt_P1 pr_g)).
apply Ropp_eq_compat.
apply RiemannInt_P18.
apply Rlt_le ; apply r.
intros.
apply Heq.
split.
rewrite (Rmin_right _ _ (Rlt_le _ _ r)).
apply Rlt_le ; apply H.
rewrite (Rmax_left _ _ (Rlt_le _ _ r)).
Admitted.

Lemma Riemann_integrable_const : forall (c a b : R), Riemann_integrable (fun x => c) a b.
Proof.
intros.
Admitted.

Lemma RiemannInt_const : forall (c a b : R) (pr : Riemann_integrable (fun x => c) a b), RiemannInt pr = c * (b-a).
Proof.
intros.
Admitted.

Lemma Riemann_integrable_plus : forall (f g : R -> R) (a b : R), Riemann_integrable f a b -> Riemann_integrable g a b -> Riemann_integrable (fun x => f x + g x) a b.
Proof.
intros f g a b pr_f pr_g.
apply (Riemann_integrable_ext (fun x => f x + 1 * g x)).
intros ; ring.
Admitted.

Lemma RiemannInt_plus : forall (f g : R -> R) (a b : R) (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b) (pr : Riemann_integrable (fun x => f x + g x) a b), RiemannInt pr = RiemannInt pr_f + RiemannInt pr_g.
Proof.
intros.
rewrite <- (Rmult_1_l (RiemannInt pr_g)).
rewrite <- (RiemannInt_P13 pr_f pr_g (RiemannInt_P10 1 pr_f pr_g)).
apply RiemannInt_ext.
Admitted.

Lemma Riemann_integrable_minus : forall (f g : R -> R) (a b : R), Riemann_integrable f a b -> Riemann_integrable g a b -> Riemann_integrable (fun x => f x - g x) a b.
Proof.
intros f g a b pr_f pr_g.
apply (Riemann_integrable_ext (fun x => f x + (-1) * g x)).
intros ; ring.
Admitted.

Lemma RiemannInt_minus : forall (f g : R -> R) (a b : R) (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b) (pr : Riemann_integrable (fun x => f x - g x) a b), RiemannInt pr = RiemannInt pr_f - RiemannInt pr_g.
Proof.
intros.
rewrite <- (Rmult_1_l (RiemannInt pr_g)).
unfold Rminus.
rewrite <- Ropp_mult_distr_l_reverse.
rewrite -(RiemannInt_P13 pr_f pr_g (RiemannInt_P10 (-1) pr_f pr_g)).
apply RiemannInt_ext.
Admitted.

Lemma Riemann_integrable_opp : forall (f : R -> R) (a b : R), Riemann_integrable f a b -> Riemann_integrable (fun x => - f x) a b.
Proof.
intros f a b pr_f.
apply (Riemann_integrable_ext (fun x => 0 + (-1) * f x)).
intros ; ring.
Admitted.

Lemma RiemannInt_opp : forall (f : R -> R) (a b : R) (pr_f : Riemann_integrable f a b) (pr : Riemann_integrable (fun x => - f x) a b), RiemannInt pr = - RiemannInt pr_f.
Proof.
intros.
rewrite <- (Rmult_1_l (RiemannInt pr_f)).
rewrite <- Ropp_mult_distr_l_reverse.
rewrite -(Rplus_0_l (-1 * RiemannInt pr_f)).
assert (0 = RiemannInt (Riemann_integrable_const 0 a b)).
rewrite RiemannInt_const.
ring.
rewrite H ; clear H.
rewrite <- (RiemannInt_P13 (Riemann_integrable_const 0 _ _) pr_f (RiemannInt_P10 (-1) (Riemann_integrable_const 0 a b) pr_f)).
apply RiemannInt_ext.
Admitted.

Lemma Riemann_integrable_scal : forall (f : R -> R) (a b c : R), Riemann_integrable f a b -> Riemann_integrable (fun x => c * f x) a b.
Proof.
intros f a b c pr_f.
apply (Riemann_integrable_ext (fun x => 0 + c * f x)).
intros ; ring.
Admitted.

Lemma RiemannInt_scal : forall (f : R -> R) (a b c : R) (pr_f : Riemann_integrable f a b) (pr : Riemann_integrable (fun x => c * f x) a b), RiemannInt pr = c * RiemannInt pr_f.
Proof.
intros.
rewrite <- (Rplus_0_l (c * RiemannInt pr_f)).
assert (0 = RiemannInt (Riemann_integrable_const 0 a b)).
rewrite RiemannInt_const.
ring.
rewrite H ; clear H.
rewrite <- (RiemannInt_P13 (Riemann_integrable_const 0 _ _) pr_f (RiemannInt_P10 (c) (Riemann_integrable_const 0 a b) pr_f)).
apply RiemannInt_ext.
Admitted.

Lemma ln_pow x n : 0 < x -> ln (x^n) = INR n * ln x.
intro Hx ; induction n as [ | n IH].
rewrite pow_O ln_1 ; simpl ; ring.
rewrite S_INR ; simpl ; rewrite ln_mult ; try intuition.
Admitted.

Lemma ln_le x y : 0 < x -> x <= y -> ln x <= ln y.
Proof.
intros Hx Hxy ; destruct Hxy.
left ; apply ln_increasing.
exact Hx.
exact H.
Admitted.

Lemma ln_div x y : 0 < x -> 0 < y -> ln (x / y) = ln x - ln y.
Proof.
intros Hx Hy ; unfold Rdiv.
rewrite ln_mult.
rewrite ln_Rinv.
ring.
exact Hy.
exact Hx.
Admitted.

Lemma derivable_pt_lim_atan : forall x, derivable_pt_lim atan x (/(1 + x^2)).
Proof.
intros x.
apply derive_pt_eq_1 with (derivable_pt_atan x).
replace (x ^ 2) with (x * x) by ring.
rewrite -(Rmult_1_l (Rinv _)).
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
apply Rle_trans with (1 := IH h0 h''0), RmaxLess2.

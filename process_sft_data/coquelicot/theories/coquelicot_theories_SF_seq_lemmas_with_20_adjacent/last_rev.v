Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool.
Require Import Rcomplements Rbar Lub.
Require Import Hierarchy.
Open Scope R_scope.
Fixpoint seq2Rlist (s : seq R) := match s with | [::] => RList.nil | h::t => RList.cons h (seq2Rlist t) end.
Fixpoint Rlist2seq (s : Rlist) : seq R := match s with | RList.nil => [::] | RList.cons h t => h::(Rlist2seq t) end.
Fixpoint sorted {T : Type} (Ord : T -> T -> Prop) (s : seq T) := match s with | [::] | [:: _] => True | h0 :: (h1 :: t1) as t0 => Ord h0 h1 /\ sorted Ord t0 end.
Definition seq_step (s : seq R) := foldr Rmax 0 (pairmap (fun x y => Rabs (Rminus y x)) (head 0 s) (behead s)).
Section SF_seq.
Context {T : Type}.
Record SF_seq := mkSF_seq {SF_h : R ; SF_t : seq (R * T)}.
Definition SF_lx (s : SF_seq) : seq R := (SF_h s)::(unzip1 (SF_t s)).
Definition SF_ly (s : SF_seq) : seq T := unzip2 (SF_t s).
Definition SF_make (lx : seq R) (ly : seq T) (Hs : size lx = S (size ly)) : SF_seq := mkSF_seq (head 0 lx) (zip (behead lx) ly).
Definition SF_nil (x0 : R) : SF_seq := mkSF_seq x0 [::].
Definition SF_cons (h : R*T) (s : SF_seq) := mkSF_seq (fst h) ((SF_h s,snd h)::(SF_t s)).
Definition SF_rcons (s : SF_seq) (t : R*T) := mkSF_seq (SF_h s) (rcons (SF_t s) t).
Definition SF_size (s : SF_seq) := size (SF_t s).
Definition SF_rev (s : SF_seq) : SF_seq := SF_make (rev (SF_lx s)) (rev (SF_ly s)) (SF_rev_0 s).
Definition SF_cat (x y : SF_seq) := mkSF_seq (SF_h x) ((SF_t x) ++ (SF_t y)).
Definition SF_head (y0 : T) (s : SF_seq) := (SF_h s, head y0 (SF_ly s)).
Definition SF_behead (s : SF_seq) := mkSF_seq (head (SF_h s) (unzip1 (SF_t s))) (behead (SF_t s)).
Definition SF_last y0 (s : SF_seq) : (R*T) := last (SF_h s,y0) (SF_t s).
Definition SF_belast (s : SF_seq) : SF_seq := mkSF_seq (SF_h s) (Rcomplements.belast (SF_t s)).
Definition SF_sorted (Ord : R -> R -> Prop) (s : SF_seq) := sorted Ord (SF_lx s).
End SF_seq.
Section SF_map.
Context {T T0 : Type}.
Definition SF_map (f : T -> T0) (s : SF_seq) : SF_seq := mkSF_seq (SF_h s) (map (fun x => (fst x,f (snd x))) (SF_t s)).
End SF_map.
Definition pointed_subdiv (ptd : @SF_seq R) := forall i : nat, (i < SF_size ptd)%nat -> nth 0 (SF_lx ptd) i <= nth 0 (SF_ly ptd) i <= nth 0 (SF_lx ptd) (S i).
Fixpoint seq_cut_down (s : seq (R*R)) (x : R) : seq (R*R) := match s with | [::] => [:: (x,x)] | h :: t => match Rle_dec (fst h) x with | right _ => [:: (x,Rmin (snd h) x)] | left _ => h :: (seq_cut_down t x) end end.
Fixpoint seq_cut_up (s : seq (R*R)) (x : R) : seq (R*R) := match s with | [::] => [:: (x,x)] | h :: t => match Rle_dec (fst h) x with | right _ => (x,x)::(fst h,Rmax (snd h) x)::t | left _ => seq_cut_up t x end end.
Definition SF_cut_down (sf : @SF_seq R) (x : R) := let s := seq_cut_down ((SF_h sf,SF_h sf) :: (SF_t sf)) x in mkSF_seq (fst (head (SF_h sf,SF_h sf) s)) (behead s).
Definition SF_cut_up (sf : @SF_seq R) (x : R) := let s := seq_cut_up ((SF_h sf,SF_h sf) :: (SF_t sf)) x in mkSF_seq (fst (head (SF_h sf,SF_h sf) s)) (behead s).
Section SF_fun.
Context {T : Type}.
Fixpoint SF_fun_aux (h : R*T) (s : seq (R*T)) (y0 : T) (x : R) := match s with | [::] => match Rle_dec x (fst h) with | left _ => snd h | right _ => y0 end | h0 :: s0 => match Rlt_dec x (fst h) with | left _ => snd h | right _ => SF_fun_aux h0 s0 y0 x end end.
Definition SF_fun (s : SF_seq) (y0 : T) (x : R) := SF_fun_aux (SF_h s,y0) (SF_t s) y0 x.
End SF_fun.
Definition SF_seq_f1 {T : Type} (f1 : R -> T) (P : seq R) : SF_seq := mkSF_seq (head 0 P) (pairmap (fun x y => (y, f1 x)) (head 0 P) (behead P)).
Definition SF_seq_f2 {T : Type} (f2 : R -> R -> T) (P : seq R) : SF_seq := mkSF_seq (head 0 P) (pairmap (fun x y => (y, f2 x y)) (head 0 P) (behead P)).
Definition SF_fun_f1 {T : Type} (f1 : R -> T) (P : seq R) x : T := SF_fun (SF_seq_f1 f1 P) (f1 0) x.
Definition SF_fun_f2 {T : Type} (f2 : R -> R -> T) (P : seq R) x := SF_fun (SF_seq_f2 f2 P) (f2 0 0) x.
Definition unif_part (a b : R) (n : nat) : seq R := mkseq (fun i => a + (INR i) * (b - a) / (INR n + 1)) (S (S n)).
Definition SF_val_seq {T} (f : R -> T) (a b : R) (n : nat) : SF_seq := SF_seq_f2 (fun x y => f ((x+y)/2)) (unif_part a b n).
Definition SF_val_fun {T} (f : R -> T) (a b : R) (n : nat) (x : R) : T := SF_fun_f2 (fun x y => f ((x+y)/2)) (unif_part a b n) x.
Definition SF_val_ly {T} (f : R -> T) (a b : R) (n : nat) : seq T := behead (pairmap (fun x y => f ((x+y)/2)) 0 (unif_part a b n)).
Definition Riemann_fine (a b : R) := within (fun ptd => pointed_subdiv ptd /\ SF_h ptd = Rmin a b /\ last (SF_h ptd) (SF_lx ptd) = Rmax a b) (locally_dist (fun ptd => seq_step (SF_lx ptd))).
Global Instance Riemann_fine_filter : forall a b, ProperFilter (Riemann_fine a b).
Proof.
intros a b.
constructor.
-
intros P [alpha H].
assert (Hab : Rmin a b <= Rmax a b).
apply Rmax_case.
apply Rmin_l.
apply Rmin_r.
assert (Hn : 0 <= ((Rmax a b - Rmin a b) / alpha)).
apply Rdiv_le_0_compat.
apply -> Rminus_le_0.
apply Hab.
apply cond_pos.
set n := (nfloor _ Hn).
exists (SF_seq_f2 (fun x y => x) (unif_part (Rmin a b) (Rmax a b) n)).
destruct (Riemann_fine_unif_part (fun x y => x) (Rmin a b) (Rmax a b) n).
intros u v Huv.
split.
apply Rle_refl.
exact Huv.
exact Hab.
apply H.
apply Rle_lt_trans with (1 := H0).
apply Rlt_div_l.
apply INRp1_pos.
unfold n, nfloor.
destruct nfloor_ex as [n' Hn'].
simpl.
rewrite Rmult_comm.
apply Rlt_div_l.
apply cond_pos.
apply Hn'.
exact H1.
-
apply within_filter.
apply locally_dist_filter.
Section Riemann_sum.
Context {V : ModuleSpace R_Ring}.
Definition Riemann_sum (f : R -> V) (ptd : SF_seq) : V := foldr plus zero (pairmap (fun x y => (scal (fst y - fst x) (f (snd y)))) (SF_h ptd,zero) (SF_t ptd)).
End Riemann_sum.
Section Riemann_sum_Normed.
Context {V : NormedModule R_AbsRing}.
End Riemann_sum_Normed.
Section RInt_val.
Context {V : ModuleSpace R_Ring}.
Definition RInt_val (f : R -> V) (a b : R) (n : nat) := Riemann_sum f (SF_seq_f2 (fun x y => (x + y) / 2) (unif_part a b n)).
End RInt_val.
Fixpoint seq_cut_down' (s : seq (R*R)) (x x0 : R) : seq (R*R) := match s with | [::] => [:: (x,x0)] | h :: t => match Rle_dec (fst h) x with | right _ => [:: (x,snd h)] | left _ => h :: (seq_cut_down' t x (snd h)) end end.
Fixpoint seq_cut_up' (s : seq (R*R)) (x x0 : R) : seq (R*R) := match s with | [::] => [:: (x,x0)] | h :: t => match Rle_dec (fst h) x with | right _ => (x,x0)::h::t | left _ => seq_cut_up' t x (snd h) end end.
Definition SF_cut_down' (sf : @SF_seq R) (x : R) x0 := let s := seq_cut_down' ((SF_h sf,x0) :: (SF_t sf)) x x0 in mkSF_seq (fst (head (SF_h sf,x0) s)) (behead s).
Definition SF_cut_up' (sf : @SF_seq R) (x : R) x0 := let s := seq_cut_up' ((SF_h sf,x0) :: (SF_t sf)) x x0 in mkSF_seq (fst (head (SF_h sf,x0) s)) (behead s).
Definition SF_compat_le (s : @SF_seq R) (pr : SF_sorted Rle s) : StepFun (head 0 (SF_lx s)) (last 0 (SF_lx s)).
Proof.
exists (SF_fun s 0) ; exists (seq2Rlist (SF_lx s)) ; exists (seq2Rlist (SF_ly s)).
by apply ad_SF_compat.
Defined.
Definition sf_SF_val_fun (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
case : (Rle_dec a b) => Hab.
exists (SF_val_fun f a b n) ; exists (seq2Rlist (unif_part a b n)) ; exists (seq2Rlist (SF_val_ly f a b n)) ; by apply ad_SF_val_fun.
exists (SF_val_fun f b a n) ; exists (seq2Rlist (unif_part b a n)) ; exists (seq2Rlist (SF_val_ly f b a n)) ; by apply ad_SF_val_fun.
Defined.
Definition Sup_fct (f : R -> R) (a b : R) : Rbar := match Req_EM_T a b with | right Hab => Lub_Rbar (fun y => exists x, y = f x /\ Rmin a b < x < Rmax a b) | left _ => Finite 0 end.
Definition Inf_fct (f : R -> R) (a b : R) : Rbar := match Req_EM_T a b with | right Hab => Glb_Rbar (fun y => exists x, y = f x /\ Rmin a b < x < Rmax a b) | left _ => Finite 0 end.
Definition SF_sup_seq (f : R -> R) (a b : R) (n : nat) : SF_seq := SF_seq_f2 (Sup_fct f) (unif_part a b n).
Definition SF_inf_seq (f : R -> R) (a b : R) (n : nat) : SF_seq := SF_seq_f2 (Inf_fct f) (unif_part a b n).
Definition SF_sup_fun (f : R -> R) (a b : R) (n : nat) (x : R) : Rbar := match (Rle_dec a b) with | left _ => SF_fun (SF_sup_seq f a b n) (Finite 0) x | right _ => SF_fun (SF_sup_seq f b a n) (Finite 0) x end.
Definition SF_inf_fun (f : R -> R) (a b : R) (n : nat) (x : R) : Rbar := match (Rle_dec a b) with | left _ => SF_fun (SF_inf_seq f a b n) (Finite 0) x | right _ => SF_fun (SF_inf_seq f b a n) (Finite 0) x end.
Definition SF_sup_r (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
exists (fun x => real (SF_sup_fun f a b n x)) ; case : (Rle_dec a b) => Hab.
exists (seq2Rlist (unif_part a b n)) ; exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part a b n)))) ; by apply ad_SF_sup_r.
exists (seq2Rlist ((unif_part b a n))) ; exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part b a n)))) ; by apply ad_SF_sup_r.
Defined.
Definition SF_inf_r (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
exists (fun x => real (SF_inf_fun f a b n x)) ; case : (Rle_dec a b) => Hab.
exists (seq2Rlist (unif_part a b n)) ; exists (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part a b n)))) ; by apply ad_SF_inf_r.
exists (seq2Rlist ((unif_part b a n))) ; exists (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part b a n)))) ; by apply ad_SF_inf_r.
Defined.

Lemma seq2Rlist_bij (s : Rlist) : seq2Rlist (Rlist2seq s) = s.
Proof.
Admitted.

Lemma Rlist2seq_bij (s : seq R) : Rlist2seq (seq2Rlist s) = s.
Proof.
Admitted.

Lemma size_compat (s : seq R) : Rlength (seq2Rlist s) = size s.
Proof.
Admitted.

Lemma nth_compat (s : seq R) (n : nat) : pos_Rl (seq2Rlist s) n = nth 0 s n.
Proof.
Admitted.

Lemma rev_rev {T} (l : seq T) : rev (rev l) = l.
Proof.
elim: l => /= [ | h l IH].
by [].
Admitted.

Lemma head_rev {T} (x0 : T) (l : seq T) : head x0 (rev l) = last x0 l.
Proof.
elim: l x0 => /= [ | x1 l IH] x0.
by [].
Admitted.

Lemma last_unzip1 {S T} x0 y0 (s : seq (S * T)) : last x0 (unzip1 s) = fst (last (x0,y0) s).
Proof.
case: s => [ | h s] //= .
Admitted.

Lemma sorted_nth {T : Type} (Ord : T -> T -> Prop) (s : seq T) : sorted Ord s <-> (forall i : nat, (i < Peano.pred (size s))%nat -> forall x0 : T, Ord (nth x0 s i) (nth x0 s (S i))).
Proof.
case: s.
split => // _ i Hi ; contradict Hi ; apply lt_n_O.
move => t s ; elim: s t => [ t | t s IHs t0] ; split => // H.
move => i Hi ; contradict Hi ; apply lt_n_O.
case => [| i] Hi x0 ; simpl in Hi.
apply H.
case: (IHs t) => {IHs} IHs _ ; apply (IHs (proj2 H) i (lt_S_n _ _ Hi) x0).
split.
apply (H O (lt_0_Sn _) t).
case: (IHs t) => {IHs} _ IHs.
Admitted.

Lemma sorted_cat {T : Type} (Ord : T -> T -> Prop) (s1 s2 : seq T) x0 : sorted Ord s1 -> sorted Ord s2 -> Ord (last x0 s1) (head x0 s2) -> sorted Ord (s1 ++ s2).
Proof.
move/sorted_nth => H1.
move/sorted_nth => H2 H0.
apply sorted_nth => i Hi => x1.
rewrite ?nth_cat.
rewrite ?SSR_minus.
case: (le_dec (S i) (size s1)) => Hi0.
move: (proj2 (SSR_leq _ _) Hi0) ; case: (ssrnat.leq (S i) (size s1)) => // _.
case: (le_dec (S (S i)) (size s1)) => Hi1.
move: (proj2 (SSR_leq _ _) Hi1) ; case: (ssrnat.leq (S (S i)) (size s1)) => // _.
apply H1 ; intuition.
have : ~ (ssrnat.leq (S (S i)) (size s1)).
contradict Hi1 ; by apply SSR_leq.
case: (ssrnat.leq (S (S i)) (size s1)) => // _.
suff Hi' : i = Peano.pred (size s1).
rewrite Hi' nth_last.
replace (S (Peano.pred (size s1)) - size s1)%nat with O.
rewrite nth0.
apply not_le in Hi1.
case: (s1) H0 Hi Hi' Hi0 Hi1 => [ | x2 s1'] //= H0 Hi Hi' Hi0 Hi1.
by apply le_Sn_O in Hi0.
case: (s2) H0 Hi0 Hi => [ | x3 s2'] //= H0 Hi0 Hi.
rewrite cats0 /= in Hi.
rewrite Hi' in Hi.
by apply lt_irrefl in Hi.
case: (s1) Hi0 => //= [ | x2 s0] Hi0.
by apply le_Sn_O in Hi0.
by rewrite minus_diag.
apply sym_eq, le_antisym.
apply MyNat.le_pred_le_succ.
apply not_le in Hi1.
by apply lt_n_Sm_le.
replace i with (Peano.pred (S i)) by auto.
by apply le_pred.
have : ~ (ssrnat.leq (S i) (size s1)).
contradict Hi0 ; by apply SSR_leq.
case: (ssrnat.leq (S i) (size s1)) => // _.
have : ~ssrnat.leq (S (S i)) (size s1).
contradict Hi0.
apply SSR_leq in Hi0.
intuition.
case: (ssrnat.leq (S (S i)) (size s1)) => // _.
replace (S i - size s1)%nat with (S (i - size s1)).
apply H2.
rewrite size_cat in Hi.
apply not_le in Hi0.
elim: (size s1) i Hi Hi0 => [ | n IH] /= i Hi Hi0.
rewrite -minus_n_O.
unfold ssrnat.addn, ssrnat.addn_rec in Hi.
by rewrite plus_0_l in Hi.
case: i Hi Hi0 => [ | i] /= Hi Hi0.
by apply lt_S_n, lt_n_O in Hi0.
apply IH ; by intuition.
apply not_le in Hi0.
Admitted.

Lemma sorted_head (s : seq R) i : sorted Rle s -> (i < size s)%nat -> forall x0, head x0 s <= nth x0 s i.
Proof.
case: s => [| h s].
move => _ Hi ; by apply lt_n_O in Hi.
elim: s h i => [| h0 s IH] h i Hs Hi x0.
apply lt_n_Sm_le, le_n_O_eq in Hi ; rewrite -Hi ; apply Rle_refl.
case: i Hi => [| i] Hi.
apply Rle_refl.
apply Rle_trans with (r2 := head x0 (h0::s)).
apply Hs.
apply IH.
apply Hs.
Admitted.

Lemma sorted_incr (s : seq R) i j : sorted Rle s -> (i <= j)%nat -> (j < size s)%nat -> forall x0, nth x0 s i <= nth x0 s j.
Proof.
elim: i j s => [| i IH] j s Hs Hij Hj x0.
rewrite nth0 ; by apply sorted_head.
case: j Hij Hj => [| j] Hij Hj.
by apply le_Sn_O in Hij.
case: s Hs Hj => [| h s] Hs Hj.
by apply lt_n_O in Hj.
apply (IH j s) with (x0 := x0) => //.
case: (s) Hs => {s Hj} [| h0 s] Hs ; apply Hs.
apply le_S_n, Hij.
Admitted.

Lemma sorted_last (s : seq R) i : sorted Rle s -> (i < size s)%nat -> forall x0, nth x0 s i <= last x0 s.
Proof.
move => Hs Hi x0 ; rewrite -nth_last.
case: s Hi Hs => [| h s] Hi Hs //.
by apply lt_n_O in Hi.
apply sorted_incr => //.
Admitted.

Lemma sorted_dec (s : seq R) x0 (x : R) : sorted Rle s -> head x0 s <= x <= last x0 s -> {i : nat | nth x0 s i <= x < nth x0 s (S i) /\ (S (S i) < size s)%nat} + {nth x0 s (size s - 2)%nat <= x <= nth x0 s (size s - 1)%nat}.
Proof.
case: s => [/= _ Hx| h s] ; simpl minus ; rewrite -?minus_n_O.
by right.
case: s => [/= _ Hx| h0 s] ; simpl minus ; rewrite -?minus_n_O.
by right.
elim: s h h0 => [/= | h1 s IH] h h0 Hs Hx.
by right.
case: (Rlt_le_dec x h0) => Hx'.
left ; exists O => /= ; intuition.
case: (IH h0 h1) => [ | |[i Hi]|Hi].
apply Hs.
split ; [apply Hx'|apply Hx].
left ; exists (S i) => /= ; intuition.
right => /= ; simpl in Hi.
Admitted.

Lemma sorted_compat (s : seq R) : sorted Rle s <-> ordered_Rlist (seq2Rlist s).
Proof.
case: s => [| h s].
split => // H i /= Hi ; contradict Hi ; apply lt_n_O.
elim: s h => [h | h s IHs h'].
split => // H i /= Hi ; contradict Hi ; apply lt_n_O.
split => H.
case => [ /= | i] ; rewrite size_compat => Hi ; simpl in Hi.
apply H.
apply (proj1 (IHs h) (proj2 H) i) ; rewrite size_compat /= ; apply lt_S_n => //.
split.
apply (H O) ; rewrite size_compat /= ; apply lt_O_Sn.
Admitted.

Lemma seq_step_ge_0 x : (0 <= seq_step x).
Proof.
clear ; unfold seq_step ; case: x => [ | x0 x] //= .
by apply Rle_refl.
elim: x x0 => [ | x1 x IH] //= x0.
by apply Rle_refl.
apply Rmax_case.
by apply Rabs_pos.
Admitted.

Lemma seq_step_cat (x y : seq R) : (0 < size x)%nat -> (0 < size y)%nat -> last 0 x = head 0 y -> seq_step (cat x (behead y)) = Rmax (seq_step x) (seq_step y).
Proof.
case: x => /= [ H | x0 x _].
by apply lt_irrefl in H.
case: y => /= [ H | y0 y _].
by apply lt_irrefl in H.
move => <-.
elim: x y x0 {y0} => /= [ | x1 x IH] y x0.
rewrite {2}/seq_step /=.
rewrite /Rmax ; case: Rle_dec (seq_step_ge_0 (x0 :: y)) => // _ _.
unfold seq_step ; simpl.
rewrite -Rmax_assoc.
apply f_equal.
Admitted.

Lemma seq_step_rev (l : seq R) : seq_step (rev l) = seq_step l.
Proof.
rewrite /seq_step.
rewrite head_rev behead_rev /=.
case: l => [ | x0 l] //=.
case: l => [ | x1 l] //=.
rewrite rev_cons.
case: l => [ | x2 l] //=.
by rewrite -Rabs_Ropp Ropp_minus_distr'.
rewrite rev_cons pairmap_rcons foldr_rcons.
rewrite -Rabs_Ropp Ropp_minus_distr'.
generalize (Rabs (x1 - x0)) ; clear.
elim: l x1 x2 => [ | x2 l IH] x0 x1 r //=.
rewrite -Rabs_Ropp Ropp_minus_distr' !Rmax_assoc.
apply f_equal2 => //.
by apply Rmax_comm.
rewrite rev_cons pairmap_rcons foldr_rcons.
rewrite -Rabs_Ropp Ropp_minus_distr' Rmax_assoc IH.
Admitted.

Lemma nth_le_seq_step x0 (l : seq R) (i : nat) : (S i < size l)%nat -> Rabs (nth x0 l (S i) - nth x0 l i) <= seq_step l.
Proof.
elim: i l => [ | i IH] ; case => [ | x1 l] /= Hi.
by apply lt_n_O in Hi.
apply lt_S_n in Hi.
destruct l as [ | x2 l].
by apply lt_n_O in Hi.
by apply Rmax_l.
by apply lt_n_O in Hi.
apply lt_S_n in Hi.
move: (IH l Hi).
destruct l as [ | x2 l] ; simpl.
by apply lt_n_O in Hi.
simpl in Hi ; apply lt_S_n in Hi.
move => {IH} IH.
eapply Rle_trans.
by apply IH.
Admitted.

Lemma SF_size_lx_ly (s : SF_seq) : size (SF_lx s) = S (size (SF_ly s)).
Proof.
Admitted.

Lemma SF_seq_bij (s : SF_seq) : SF_make (SF_lx s) (SF_ly s) (SF_size_lx_ly s) = s.
Proof.
Admitted.

Lemma SF_seq_bij_lx (lx : seq R) (ly : seq T) (Hs : size lx = S (size ly)) : SF_lx (SF_make lx ly Hs) = lx.
Proof.
Admitted.

Lemma SF_seq_bij_ly (lx : seq R) (ly : seq T) (Hs : size lx = S (size ly)) : SF_ly (SF_make lx ly Hs) = ly.
Proof.
Admitted.

Lemma SF_cons_dec (P : SF_seq -> Type) : (forall x0 : R, P (SF_nil x0)) -> (forall h s, P (SF_cons h s)) -> (forall s, P s).
Proof.
move => Hnil Hcons [sh st] ; case: st => [| h sf].
apply Hnil.
Admitted.

Lemma SF_cons_ind (P : SF_seq -> Type) : (forall x0 : R, P (SF_nil x0)) -> (forall h s, P s -> P (SF_cons h s)) -> (forall s, P s).
Proof.
move => Hnil Hcons [sh st] ; elim: st sh => [sh |h sf IHst sh].
apply Hnil.
move: (IHst (fst h)) => {IHst} IHst.
Admitted.

Lemma SF_rcons_dec (P : SF_seq -> Type) : (forall x0 : R, P (SF_nil x0)) -> (forall s t, P (SF_rcons s t)) -> (forall s, P s).
Proof.
move => Hnil Hrcons [sh st] ; move: st ; apply rcons_dec => [| st t].
apply Hnil.
Admitted.

Lemma SF_rcons_ind (P : SF_seq -> Type) : (forall x0 : R, P (SF_nil x0)) -> (forall s t, P s -> P (SF_rcons s t)) -> (forall s, P s).
Proof.
move => Hnil Hrcons [sh st] ; move: st sh ; apply (rcons_ind (fun st => forall sh, P {| SF_h := sh; SF_t := st |})) => [sh | st t IHst sh].
apply Hnil.
Admitted.

Lemma last_rev {T} (x0 : T) (l : seq T) : last x0 (rev l) = head x0 l.
Proof.
by rewrite -head_rev rev_rev.

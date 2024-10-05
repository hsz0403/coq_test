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

Lemma SF_rev_inj (s s0 : SF_seq) : SF_rev s = SF_rev s0 -> s = s0.
Proof.
Admitted.

Lemma SF_lx_cat (x y : SF_seq) : SF_lx (SF_cat x y) = (SF_lx x) ++ (behead (SF_lx y)).
Proof.
unfold SF_cat, SF_lx ; simpl.
apply f_equal.
Admitted.

Lemma SF_last_cat (x y : SF_seq) : last (SF_h x) (SF_lx x) = head (SF_h y) (SF_lx y) -> last (SF_h (SF_cat x y)) (SF_lx (SF_cat x y)) = (last (SF_h y) (SF_lx y)).
Proof.
rewrite SF_lx_cat.
unfold SF_cat, SF_lx ; simpl => <- /=.
Admitted.

Lemma SF_cons_cat x0 (x y : SF_seq) : SF_cons x0 (SF_cat x y) = SF_cat (SF_cons x0 x) y.
Proof.
Admitted.

Lemma SF_last_lx x0 (s : SF_seq) : fst (SF_last x0 s) = last 0 (SF_lx s).
Proof.
rewrite /SF_last /=.
Admitted.

Lemma SF_map_cons (f : T -> T0) (h : R*T) (s : SF_seq) : SF_map f (SF_cons h s) = SF_cons (fst h, f (snd h)) (SF_map f s).
Proof.
Admitted.

Lemma SF_map_rcons (f : T -> T0) (s : SF_seq) (h : R*T) : SF_map f (SF_rcons s h) = SF_rcons (SF_map f s) (fst h, f (snd h)).
Proof.
move: h ; apply SF_cons_ind with (s := s) => {s} [x0 | h0 s IH] //= h.
rewrite SF_map_cons.
replace (SF_rcons (SF_cons h0 s) h) with (SF_cons h0 (SF_rcons s h)) by auto.
rewrite SF_map_cons.
rewrite IH.
Admitted.

Lemma SF_map_lx (f : T -> T0) (s : SF_seq) : SF_lx (SF_map f s) = SF_lx s.
Proof.
Admitted.

Lemma SF_map_ly (f : T -> T0) (s : SF_seq) : SF_ly (SF_map f s) = map f (SF_ly s).
Proof.
Admitted.

Lemma SF_map_rev (f : T -> T0) s : SF_rev (SF_map f s) = SF_map f (SF_rev s).
Proof.
apply SF_lx_ly_inj.
by rewrite SF_lx_rev ?SF_map_lx ?SF_lx_rev.
Admitted.

Lemma SF_size_map (f : T -> T0) s : SF_size (SF_map f s) = SF_size s.
Proof.
Admitted.

Lemma ptd_cons h s : pointed_subdiv (SF_cons h s) -> pointed_subdiv s.
Proof.
Admitted.

Lemma ptd_sort ptd : pointed_subdiv ptd -> SF_sorted Rle ptd.
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd] ; [ | apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd] IH] => Hptd ; try split => //=.
apply Rle_trans with y0 ; apply (Hptd O) ; rewrite SF_size_cons ; apply lt_O_Sn.
apply Rle_trans with y0 ; apply (Hptd O) ; rewrite SF_size_cons ; apply lt_O_Sn.
Admitted.

Lemma ptd_sort' ptd : pointed_subdiv ptd -> sorted Rle (SF_ly ptd).
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd] ; [ | apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd] IH] => Hptd ; try split.
apply Rle_trans with x1 ; [apply (Hptd O) | apply (Hptd 1%nat)] ; rewrite ?SF_size_cons ; repeat apply lt_n_S ; apply lt_O_Sn.
Admitted.

Lemma SF_cat_pointed (x y : SF_seq) : last (SF_h x) (SF_lx x) = head (SF_h y) (SF_lx y) -> pointed_subdiv x -> pointed_subdiv y -> pointed_subdiv (SF_cat x y).
Proof.
intros Hxy Hx Hy.
move: Hxy Hx.
apply (SF_cons_ind (fun x => last (SF_h x) (SF_lx x) = head (SF_h y) (SF_lx y) -> pointed_subdiv x -> pointed_subdiv (SF_cat x y))) => {x} /= [x0 | x0 x IH] Hxy Hx.
rewrite Hxy.
by apply Hy.
rewrite -SF_cons_cat.
case => [ | i] Hi.
apply (Hx O), lt_O_Sn.
apply IH =>//.
by apply ptd_cons with x0.
Admitted.

Lemma SF_cut_down_step s x eps : SF_h s <= x <= last (SF_h s) (SF_lx s) -> seq_step (SF_lx s) < eps -> seq_step (SF_lx (SF_cut_down s x)) < eps.
Proof.
unfold SF_cut_down, seq_step ; simpl.
case => Hh Hl.
case: Rle_dec => //= _.
move: Hh Hl ; apply SF_cons_ind with (s := s) => {s} [ x1 | [x1 y0] s IH ] /= Hx Hh Hl.
rewrite (Rle_antisym _ _ Hx Hh) Rminus_eq_0 Rabs_R0.
rewrite /Rmax ; by case: Rle_dec.
case: Rle_dec => //= Hx'.
apply Rmax_case.
apply Rle_lt_trans with (2 := Hl) ; by apply Rmax_l.
apply IH ; try assumption.
apply Rle_lt_trans with (2 := Hl) ; by apply Rmax_r.
apply Rle_lt_trans with (2 := Hl).
apply Rmax_case ; apply Rle_trans with (2 := Rmax_l _ _).
rewrite ?Rabs_pos_eq.
apply Rplus_le_compat_r.
by apply Rlt_le, Rnot_le_lt.
rewrite -Rminus_le_0.
apply Rle_trans with x.
by [].
by apply Rlt_le, Rnot_le_lt.
by rewrite -Rminus_le_0.
Admitted.

Lemma SF_cut_up_step s x eps : SF_h s <= x <= last (SF_h s) (SF_lx s) -> seq_step (SF_lx s) < eps -> seq_step (SF_lx (SF_cut_up s x)) < eps.
Proof.
unfold SF_cut_down, seq_step ; simpl.
case => Hh Hl.
case: Rle_dec => //= _.
move: {4 5}(SF_h s) Hh Hl ; apply SF_cons_ind with (s := s) => {s} [ x1 | [x1 y0] s IH ] /= x0 Hh Hl He.
by apply He.
case: Rle_dec => //= Hx.
apply (IH x0) => //=.
apply Rle_lt_trans with (2 := He).
by apply Rmax_r.
apply Rle_lt_trans with (2 := He).
apply Rnot_le_lt in Hx.
apply Rmax_case.
apply Rle_trans with (2 := Rmax_l _ _).
rewrite ?Rabs_pos_eq.
by apply Rplus_le_compat_l, Ropp_le_contravar.
rewrite -Rminus_le_0 ; by apply Rlt_le, Rle_lt_trans with x.
rewrite -Rminus_le_0 ; by apply Rlt_le.
Admitted.

Lemma SF_cut_down_pointed s x : SF_h s <= x -> pointed_subdiv s -> pointed_subdiv (SF_cut_down s x).
Proof.
unfold SF_cut_down ; simpl.
case: Rle_dec => //= _.
apply SF_cons_ind with (s := s) => {s} [x0 | [x1 y1] s IH] /= Hx0 H.
move => i /= Hi.
unfold SF_size in Hi ; simpl in Hi.
apply lt_n_Sm_le, le_n_O_eq in Hi.
rewrite -Hi ; simpl ; split.
by [].
by apply Rle_refl.
case: Rle_dec => //= Hx1.
move: (H O (lt_O_Sn _)) => /= H0.
apply ptd_cons in H.
move: (IH Hx1 H) => {IH} IH.
rewrite /pointed_subdiv => i.
destruct i => /= Hi.
by apply H0.
apply (IH i).
apply lt_S_n, Hi.
move => i /= Hi.
unfold SF_size in Hi ; simpl in Hi.
apply lt_n_Sm_le, le_n_O_eq in Hi.
rewrite -Hi ; simpl ; split.
apply Rmin_case.
apply (H O).
by apply lt_O_Sn.
by [].
Admitted.

Lemma SF_cut_up_pointed s x : SF_h s <= x -> pointed_subdiv s -> pointed_subdiv (SF_cut_up s x).
Proof.
unfold SF_cut_up ; simpl.
case: Rle_dec => //= _.
move: {2 3}(SF_h s) ; apply SF_cons_ind with (s := s) => {s} [ x1 | [x1 y0] s IH] /= x0 Hx0 H i Hi.
by apply lt_n_O in Hi.
destruct (Rle_dec (SF_h s) x) as [Hx1|Hx1].
apply IH => //=.
move: H ; by apply ptd_cons.
destruct i ; simpl.
split.
by apply Rmax_r.
apply Rmax_case.
by apply (H O), lt_O_Sn.
by apply Rlt_le, Rnot_le_lt.
Admitted.

Lemma SF_cut_down_h s x : SF_h s <= x -> SF_h (SF_cut_down s x) = SF_h s.
Proof.
unfold SF_cut_down ; simpl.
Admitted.

Lemma SF_map_sort (f : T -> T0) (s : SF_seq) (Ord : R -> R -> Prop) : SF_sorted Ord s -> SF_sorted Ord (SF_map f s).
Proof.
unfold SF_sorted ; apply SF_cons_ind with (s := s) => {s} /= [x0 | [x0 _] /= s IH] Hs.
by [].
split.
by apply Hs.
now apply IH.

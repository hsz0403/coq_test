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

Lemma SF_cut_up_h s x : SF_h (SF_cut_up s x) = x.
Proof.
unfold SF_cut_up ; simpl.
case: Rle_dec => //= ; simpl.
move: {2 3}(SF_h s) ; apply SF_cons_ind with (s := s) => {s} [x1 | [x1 y1] s IH ] /= x0 Hx.
by [].
case: Rle_dec => //= Hx'.
Admitted.

Lemma SF_cut_down_l s x : last (SF_h (SF_cut_down s x)) (SF_lx (SF_cut_down s x)) = x.
Proof.
unfold SF_cut_down ; simpl.
case: Rle_dec => //= ; simpl.
apply SF_cons_ind with (s := s) => {s} [x1 | [x1 y1] s IH ] /= Hx.
by [].
Admitted.

Lemma SF_cut_up_l s x : x <= last (SF_h s) (SF_lx s) -> last (SF_h (SF_cut_up s x)) (SF_lx (SF_cut_up s x)) = last (SF_h s) (SF_lx s).
Proof.
unfold SF_cut_down ; simpl.
case: Rle_dec => //=.
move: {3 4}(SF_h s); apply SF_cons_ind with (s := s) => {s} [x1 | [x1 y1] s IH ] /= x0 Hx Hx'.
by apply Rle_antisym.
case: Rle_dec => //= {Hx} Hx.
Admitted.

Lemma SF_cut_down_cons_0 h ptd x : x < fst h -> SF_cut_down (SF_cons h ptd) x = SF_nil x.
Proof.
intros H0.
apply Rlt_not_le in H0.
rewrite /SF_cut_down /=.
Admitted.

Lemma SF_cut_up_cons_0 h ptd x : x < fst h -> SF_cut_up (SF_cons h ptd) x = SF_cons (x,Rmax (fst h) x) (SF_cons h ptd).
Proof.
intros H0.
apply Rlt_not_le in H0.
rewrite /SF_cut_up /=.
Admitted.

Lemma SF_cut_down_cons_1 h ptd x : fst h <= x < SF_h ptd -> SF_cut_down (SF_cons h ptd) x = SF_cons (fst h, Rmin (snd h) x) (SF_nil x).
Proof.
intros [H0 Hx0].
apply Rlt_not_le in Hx0.
rewrite /SF_cut_down /=.
case: Rle_dec => //= _.
Admitted.

Lemma SF_cut_up_cons_1 h ptd x : fst h <= x < SF_h ptd -> SF_cut_up (SF_cons h ptd) x = SF_cons (x,Rmax (snd h) x) ptd.
Proof.
intros [H0 Hx0].
apply Rlt_not_le in Hx0.
rewrite /SF_cut_up /=.
case: Rle_dec => //= _.
Admitted.

Lemma SF_cut_down_cons_2 h ptd x : fst h <= SF_h ptd <= x -> SF_cut_down (SF_cons h ptd) x = SF_cons h (SF_cut_down ptd x).
Proof.
intros [H0 Hx0].
rewrite /SF_cut_down /=.
case: Rle_dec (Rle_trans _ _ _ H0 Hx0) => //= _ _.
Admitted.

Lemma SF_cut_up_cons_2 h ptd x : fst h <= SF_h ptd <= x -> SF_cut_up (SF_cons h ptd) x = SF_cut_up ptd x.
Proof.
intros [H0 Hx0].
rewrite /SF_cut_up /=.
case: Rle_dec (Rle_trans _ _ _ H0 Hx0) => //= _ _.
case: Rle_dec => //= _.
move: {2 3}(SF_h ptd) Hx0 ; apply SF_cons_ind with (s := ptd) => {ptd H0} [ x0 | [x0 y0] ptd IH ] //= x0' Hx0.
case: Rle_dec => //= Hx1.
Admitted.

Lemma SF_fun_incr (s : SF_seq) (y0 : T) (x : R) Hs Hx : SF_fun s y0 x = match (sorted_dec (SF_lx s) 0 x Hs Hx) with | inleft H => nth y0 (SF_ly s) (proj1_sig H) | inright _ => nth y0 (SF_ly s) (SF_size s -1)%nat end.
Proof.
rewrite /SF_fun /=.
move: Hs Hx ; apply SF_cons_dec with (s := s) => {s} [/= x1 | h s] Hs /= Hx.
case: sorted_dec => /= [[i Hi]|Hi] ; rewrite /SF_ly ; case: Rle_dec => //= ; case: i Hi => //.
case: Rlt_dec => [Hx' | _].
contradict Hx' ; apply Rle_not_lt, Hx.
move: h Hs Hx ; apply SF_cons_ind with (s := s) => {s} [x1 | h0 s IH] h Hs /= Hx.
case: sorted_dec => [/= [i [Hi' Hi]] /= |Hi].
by apply lt_S_n, lt_S_n, lt_n_O in Hi.
case: Hx => Hx Hx' ; apply Rle_not_lt in Hx ; case: Rle_dec => //.
case: Rlt_dec => Hx'.
case: sorted_dec => /= [[i Hi]|Hi]/=.
case: i Hi => //= i Hi ; contradict Hx' ; apply Rle_not_lt, Rle_trans with (2 := proj1 (proj1 Hi)).
simpl in Hs ; elim: (unzip1 (SF_t s)) (fst h0) (SF_h s) (i) (proj2 Hs) (proj2 Hi) => {s IH Hs Hx Hi h h0} [| h1 s IH] h h0 n Hs Hn.
repeat apply lt_S_n in Hn ; by apply lt_n_O in Hn.
case: n Hn => [| n] Hn.
apply Rle_refl.
apply Rle_trans with (1 := proj1 Hs) => //= ; intuition.
contradict Hx' ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hi).
simpl in Hs ; elim: (unzip1 (SF_t s)) (fst h0) (SF_h s) (proj2 Hs) => {s IH Hs Hx Hi h h0} [| h1 s IH] h h0 Hs.
apply Rle_refl.
apply Rle_trans with (1 := proj1 Hs) => //= ; intuition.
have : fst h0 <= x <= last (SF_h s) (unzip1 (SF_t s)) => [ | {Hx'} Hx'].
split ; [by apply Rnot_lt_le | by apply Hx].
rewrite (IH h0 (proj2 Hs) Hx') => {IH} ; case: sorted_dec => [[i [Hxi Hi]]|Hi] ; case: sorted_dec => [[j [Hxj Hj]]|Hj] ; rewrite -?minus_n_O //=.
move : h h0 i j Hs {Hx Hx'} Hxi Hi Hxj Hj ; apply SF_cons_ind with (s := s) => {s} [x1 | h1 s IH] h h0 i j Hs //= Hxi Hi Hxj Hj.
by apply lt_S_n, lt_S_n, lt_n_O in Hi.
case: j Hxj Hj => [/= | j] Hxj Hj.
case: Hxj => _ Hxj ; contradict Hxj ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hxi).
elim: (i) Hi => {i Hxi IH} //= [| i IH] Hi.
apply Rle_refl.
apply Rle_trans with (1 := IH (lt_trans _ _ _ (lt_n_Sn _) Hi)), (sorted_nth Rle) ; [apply Hs | simpl ; intuition].
case: i Hxi Hi => [/= | i] Hxi Hi.
case: j Hxj Hj => [//= | j] Hxj Hj.
case: Hxi => _ Hxi ; contradict Hxi ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hxj) ; elim: (j) Hj => {j Hxj IH} //= [| j IH] Hj.
apply Rle_refl.
apply Rle_trans with (1 := IH (lt_trans _ _ _ (lt_n_Sn _) Hj)), (sorted_nth Rle) ; [apply Hs | simpl ; intuition].
apply (IH h0 h1 i j) => //.
apply Hs.
apply lt_S_n, Hi.
apply lt_S_n, Hj.
simpl in Hxi, Hj ; case: Hxi => _ Hxi ; contradict Hxi ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hj).
move: Hi Hs ; rewrite ?SF_lx_cons /SF_lx.
elim: i (fst h) (fst h0) (SF_h s) (unzip1 (SF_t s)) => {s Hx Hx' Hj h y0 h0} [| i IH] h h0 h1 s Hi Hs.
case: s Hi Hs => [| h2 s] Hi Hs /=.
by apply lt_S_n, lt_S_n, lt_n_O in Hi.
elim: s h h0 h1 h2 {Hi} Hs => [| h3 s IH] h h0 h1 h2 Hs /=.
apply Rle_refl.
apply Rle_trans with (r2 := h2).
apply Hs.
apply (IH h0 h1).
apply (proj2 Hs).
case: s Hi Hs => [| h2 s] Hi Hs.
by apply lt_S_n, lt_S_n, lt_n_O in Hi.
apply (IH h0 h1 h2 s).
apply lt_S_n, Hi.
apply Hs.
simpl in Hxj, Hi ; case: Hxj => _ Hxj ; contradict Hxj ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hi).
move: Hj Hs ; rewrite ?SF_lx_cons /SF_lx.
rewrite -minus_n_O ; elim: j (fst h) (fst h0) (SF_h s) (unzip1 (SF_t s)) => {s Hx Hx' Hi h y0 h0} [ | j IH] h h0 h1 s Hj Hs /=.
elim: s h h0 h1 {Hj} Hs => [| h2 s IH] h h0 h1 Hs /=.
apply Rle_refl.
apply Rle_trans with (r2 := h1).
apply Hs.
apply (IH h0 h1 h2).
apply (proj2 Hs).
case: s Hj Hs => [| h2 s] Hj Hs.
by apply lt_S_n, lt_S_n, lt_S_n, lt_n_O in Hj.
apply (IH h0 h1 h2 s).
apply lt_S_n, Hj.
Admitted.

Lemma SF_fun_map {T T0 : Type} (f : T -> T0) (s : SF_seq) y0 : forall x, SF_fun (SF_map f s) (f y0) x = f (SF_fun s y0 x).
Proof.
case: s => sh st ; rewrite /SF_fun /SF_map /= ; case: st => [| h st] x /=.
by case: Rle_dec.
case: Rlt_dec => //.
elim: st sh h y0 x => [| h0 st IH] sh h y0 x Hx //=.
by case: Rle_dec.
case: Rlt_dec => // {Hx} Hx.
Admitted.

Lemma SF_cons_f1 {T : Type} (f1 : R -> T) (h : R) (P : seq R) : (0 < size P)%nat -> SF_seq_f1 f1 (h::P) = SF_cons (h,f1 h) (SF_seq_f1 f1 P).
Proof.
case: P => [ H | h0 P _] //.
Admitted.

Lemma SF_cons_f2 {T : Type} (f2 : R -> R -> T) (h : R) (P : seq R) : (0 < size P)%nat -> SF_seq_f2 f2 (h::P) = SF_cons (h,f2 h (head 0 P)) (SF_seq_f2 f2 P).
Proof.
case: P => [ H | h0 P _] //.
Admitted.

Lemma SF_size_f1 {T : Type} (f1 : R -> T) P : SF_size (SF_seq_f1 f1 P) = Peano.pred (size P).
Proof.
Admitted.

Lemma SF_size_f2 {T : Type} (f2 : R -> R -> T) P : SF_size (SF_seq_f2 f2 P) = Peano.pred (size P).
Proof.
Admitted.

Lemma SF_lx_f1 {T : Type} (f1 : R -> T) P : (0 < size P)%nat -> SF_lx (SF_seq_f1 f1 P) = P.
Proof.
elim: P => [ H | h l IH _] //=.
by apply lt_n_O in H.
case: l IH => [ | h' l] //= IH.
rewrite -{2}IH //.
Admitted.

Lemma SF_lx_f2 {T : Type} (f2 : R -> R -> T) P : (0 < size P)%nat -> SF_lx (SF_seq_f2 f2 P) = P.
Proof.
elim: P => [ H | h l IH _] //=.
by apply lt_n_O in H.
case: l IH => [ | h' l] //= IH.
rewrite -{2}IH //.
Admitted.

Lemma SF_ly_f2 {T : Type} (f2 : R -> R -> T) P : SF_ly (SF_seq_f2 f2 P) = behead (pairmap f2 0 P).
Proof.
Admitted.

Lemma SF_sorted_f1 {T : Type} (f1 : R -> T) P Ord : (sorted Ord P) <-> (SF_sorted Ord (SF_seq_f1 f1 P)).
Proof.
case: P => [ | h P] //.
rewrite /SF_sorted SF_lx_f1 //.
Admitted.

Lemma SF_sorted_f2 {T : Type} (f2 : R -> R -> T) P Ord : (sorted Ord P) <-> (SF_sorted Ord (SF_seq_f2 f2 P)).
Proof.
case: P => [ | h P] //.
rewrite /SF_sorted SF_lx_f2 //.
Admitted.

Lemma SF_rev_f2 {T : Type} (f2 : R -> R -> T) P : (forall x y, f2 x y = f2 y x) -> SF_rev (SF_seq_f2 f2 P) = SF_seq_f2 f2 (rev P).
Proof.
move => Hf2 ; apply SF_lx_ly_inj ; case: P => [ | h P] //=.
rewrite SF_lx_rev !SF_lx_f2 ?rev_cons /= 1?headI // ; by apply lt_O_Sn.
rewrite SF_ly_rev !SF_ly_f2 /= ?rev_cons.
elim: P h => [ | h0 P IH] h //=.
rewrite !rev_cons pairmap_rcons behead_rcons ?(IH h0) ?(Hf2 h h0) //.
Admitted.

Lemma SF_map_f1 {T T0 : Type} (f : T -> T0) (f1 : R -> T) P : SF_map f (SF_seq_f1 f1 P) = SF_seq_f1 (fun x => f (f1 x)) P.
Proof.
case: P => [| h P] // ; elim: P h => [| h0 P IH] h //.
rewrite ?(SF_cons_f1 _ _ (h0::P)) /= ; try intuition.
Admitted.

Lemma SF_map_f2 {T T0 : Type} (f : T -> T0) (f2 : R -> R -> T) P : SF_map f (SF_seq_f2 f2 P) = SF_seq_f2 (fun x y => f (f2 x y)) P.
Proof.
case: P => [| h P] // ; elim: P h => [| h0 P IH] h //.
rewrite ?(SF_cons_f2 _ _ (h0::P)) /= ; try intuition.
Admitted.

Lemma ptd_f2 (f : R -> R -> R) s : sorted Rle s -> (forall x y, x <= y -> x <= f x y <= y) -> pointed_subdiv (SF_seq_f2 f s).
Proof.
intros Hs Hf.
elim: s Hs => [ _ | h s].
intros i Hi.
by apply lt_n_O in Hi.
case: s => [ | h' s] IH Hs.
intros i Hi.
by apply lt_n_O in Hi.
case => [ | i] Hi.
apply Hf, Hs.
apply IH.
apply Hs.
Admitted.

Lemma unif_part_bound (a b : R) (n : nat) : unif_part a b n = rev (unif_part b a n).
Proof.
apply (@eq_from_nth R 0) ; rewrite ?size_rev ?size_mkseq => // ; move => i Hi ; apply SSR_leq in Hi.
rewrite nth_rev ?SSR_minus ?size_mkseq.
2: now apply SSR_leq.
rewrite ?nth_mkseq.
3: now apply SSR_leq.
rewrite minus_INR ?S_INR => // ; field.
apply Rgt_not_eq, INRp1_pos.
apply SSR_leq, INR_le ; rewrite ?S_INR minus_INR ?S_INR => //.
apply Rminus_le_0 ; ring_simplify.
Admitted.

Lemma unif_part_sort (a b : R) (n : nat) : a <= b -> sorted Rle (unif_part a b n).
Proof.
move => Hab ; apply sorted_nth => i Hi x0 ; rewrite ?size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ; [ |apply SSR_leq ; intuition | apply SSR_leq ; intuition ].
apply Rminus_le_0 ; field_simplify ; [| apply Rgt_not_eq ; intuition] ; rewrite ?Rdiv_1 ; apply Rdiv_le_0_compat ; intuition.
Admitted.

Lemma head_unif_part x0 (a b : R) (n : nat) : head x0 (unif_part a b n) = a.
Proof.
Admitted.

Lemma last_unif_part x0 (a b : R) (n : nat) : last x0 (unif_part a b n) = b.
Proof.
rewrite (last_nth b) size_mkseq.
replace (nth b (x0 :: unif_part a b n) (S (S n))) with (nth b (unif_part a b n) (S n)) by auto.
rewrite nth_mkseq.
rewrite S_INR ; field.
by apply Rgt_not_eq, INRp1_pos.
Admitted.

Lemma unif_part_nat (a b : R) (n : nat) (x : R) : (a <= x <= b) -> {i : nat | nth 0 (unif_part a b n) i <= x < nth 0 (unif_part a b n) (S i) /\ (S (S i) < size (unif_part a b n))%nat} + {nth 0 (unif_part a b n) (n) <= x <= nth 0 (unif_part a b n) (S n)}.
Proof.
move: (sorted_dec (unif_part a b n) 0 x) => Hdec Hx.
have Hs : sorted Rle (unif_part a b n) ; [ apply unif_part_sort, Rle_trans with (r2 := x) ; intuition | move: (Hdec Hs) => {Hdec Hs} Hdec].
have Hx' : (head 0 (unif_part a b n) <= x <= last 0 (unif_part a b n)).
by rewrite head_unif_part last_unif_part.
case: (Hdec Hx') => {Hdec Hx'} [[i Hi]|Hi].
left ; by exists i.
right ; rewrite size_mkseq /= in Hi ; intuition.
Admitted.

Lemma seq_step_unif_part (a b : R) (n : nat) : seq_step (unif_part a b n) = Rabs ((b - a) / (INR n + 1)).
Proof.
assert (forall i, (S i < size (unif_part a b n))%nat -> (nth 0 (unif_part a b n) (S i) - nth 0 (unif_part a b n) i = (b - a) / (INR n + 1))%R).
rewrite size_mkseq => i Hi.
rewrite !nth_mkseq.
rewrite S_INR /Rdiv /= ; ring.
by apply SSR_leq, lt_le_weak.
by apply SSR_leq.
move: (eq_refl (size (unif_part a b n))).
rewrite {2}size_mkseq.
rewrite /seq_step ; elim: {2}(n) (unif_part a b n) H => [ | m IH] l //= ; destruct l as [ | x0 l] => //= ; destruct l as [ | x1 l] => //= ; destruct l as [ | x2 l] => //= ; intros.
rewrite (H O).
rewrite Rmax_comm /Rmax ; case: Rle_dec => // H1.
contradict H1 ; by apply Rabs_pos.
by apply lt_n_S, lt_O_Sn.
rewrite -(IH (x1::x2::l)) /=.
rewrite (H O).
rewrite (H 1%nat).
rewrite Rmax_assoc.
apply f_equal2 => //.
rewrite /Rmax ; by case: Rle_dec.
by apply lt_n_S, lt_n_S, lt_O_Sn.
by apply lt_n_S, lt_O_Sn.
now intros ; apply (H (S i)), lt_n_S.
Admitted.

Lemma seq_step_unif_part_ex (a b : R) (eps : posreal) : {n : nat | seq_step (unif_part a b n) < eps}.
Proof.
destruct (nfloor_ex (Rabs ((b - a) / eps))) as [n Hn].
by apply Rabs_pos.
exists n.
rewrite seq_step_unif_part.
rewrite Rabs_div.
rewrite (Rabs_pos_eq (INR n + 1)).
apply Rlt_div_l.
by apply INRp1_pos.
rewrite Rmult_comm -Rlt_div_l.
rewrite -(Rabs_pos_eq eps).
rewrite -Rabs_div.
by apply Hn.
by apply Rgt_not_eq, eps.
by apply Rlt_le, eps.
by apply eps.
by apply Rlt_le, INRp1_pos.
Admitted.

Lemma unif_part_S a b n : unif_part a b (S n) = a :: unif_part ((a * INR (S n) + b) / INR (S (S n))) b n.
Proof.
apply eq_from_nth with 0.
by rewrite /= !size_map !size_iota.
case => [ | i] Hi.
by rewrite nth0 head_unif_part.
change (nth 0 (a :: unif_part ((a * INR (S n) + b) / INR (S (S n))) b n) (S i)) with (nth 0 (unif_part ((a * INR (S n) + b) / INR (S (S n))) b n) i).
rewrite /unif_part size_mkseq in Hi.
rewrite /unif_part !nth_mkseq ; try by intuition.
rewrite !S_INR ; field.
Admitted.

Lemma SF_val_ly_bound {T} (f : R -> T) (a b : R) (n : nat) : SF_val_ly f a b n = rev (SF_val_ly f b a n).
Proof.
rewrite /SF_val_ly (unif_part_bound b a).
case: (unif_part a b n) => [| h s] // ; elim: s h => [| h0 s IH] h //=.
rewrite ?rev_cons.
replace (pairmap (fun x y : R => f ((x + y) / 2)) 0 (rcons (rcons (rev s) h0) h)) with (rcons (pairmap (fun x y : R => f ((x + y) / 2)) 0 (rcons (rev s) h0)) (f ((h0+h)/2))).
rewrite behead_rcons.
rewrite rev_rcons Rplus_comm -rev_cons -IH //.
rewrite size_pairmap size_rcons ; apply lt_O_Sn.
move: (0) h h0 {IH} ; apply rcons_ind with (s := s) => {s} [| s h1 IH] x0 h h0 //.
Admitted.

Lemma Riemann_fine_unif_part : forall (f : R -> R -> R) (a b : R) (n : nat), (forall a b, a <= b -> a <= f a b <= b) -> a <= b -> seq_step (SF_lx (SF_seq_f2 f (unif_part a b n))) <= (b - a) / (INR n + 1) /\ pointed_subdiv (SF_seq_f2 f (unif_part a b n)) /\ SF_h (SF_seq_f2 f (unif_part a b n)) = a /\ last (SF_h (SF_seq_f2 f (unif_part a b n))) (SF_lx (SF_seq_f2 f (unif_part a b n))) = b.
Proof.
intros f a b n Hf Hab.
assert (Hab' : 0 <= (b - a) / (INR n + 1)).
apply Rdiv_le_0_compat.
apply -> Rminus_le_0.
apply Hab.
apply INRp1_pos.
unfold pointed_subdiv.
rewrite SF_lx_f2.
change (head 0 (unif_part a b n) :: behead (unif_part a b n)) with (unif_part a b n).
split ; [|split ; [|split]].
-
cut (forall i, (S i < size (unif_part a b n))%nat -> nth 0 (unif_part a b n) (S i) - nth 0 (unif_part a b n) i = (b - a) / (INR n + 1)).
+
induction (unif_part a b n) as [|x0 l IHl].
now intros _.
intros H.
destruct l as [|x1 l].
easy.
change (seq_step _) with (Rmax (Rabs (x1 - x0)) (seq_step (x1 :: l))).
apply Rmax_case.
apply Req_le.
rewrite (H 0%nat).
now apply Rabs_pos_eq.
apply lt_n_S.
apply lt_0_Sn.
apply IHl.
intros i Hi.
apply (H (S i)).
now apply lt_n_S.
+
rewrite size_mkseq.
intros i Hi.
rewrite !nth_mkseq.
rewrite S_INR.
unfold Rdiv.
ring.
apply SSR_leq.
now apply lt_le_weak.
now apply SSR_leq.
-
unfold pointed_subdiv.
rewrite SF_size_f2.
rewrite size_mkseq.
intros i Hi.
rewrite SF_ly_f2.
rewrite nth_behead.
apply gt_S_le, SSR_leq in Hi.
rewrite (nth_pairmap 0).
change (nth 0 (0 :: unif_part a b n) (S i)) with (nth 0 (unif_part a b n) i).
apply Hf.
rewrite !nth_mkseq //.
rewrite S_INR.
lra.
now apply ssrnat.leqW.
by rewrite size_mkseq.
-
apply head_unif_part.
-
apply last_unif_part.
Admitted.

Lemma Riemann_sum_cons (f : R -> V) (h0 : R * R) (ptd : SF_seq) : Riemann_sum f (SF_cons h0 ptd) = plus (scal (SF_h ptd - fst h0) (f (snd h0))) (Riemann_sum f ptd).
Proof.
rewrite /Riemann_sum /=.
Admitted.

Lemma Riemann_sum_rcons (f : R -> V) ptd l0 : Riemann_sum f (SF_rcons ptd l0) = plus (Riemann_sum f ptd) (scal (fst l0 - last (SF_h ptd) (SF_lx ptd)) (f (snd l0))).
Proof.
rewrite /Riemann_sum .
case: l0 => x0 y0.
apply SF_rcons_dec with (s := ptd) => {ptd} [ x1 | ptd [x1 y1]].
apply plus_comm.
rewrite ?SF_map_rcons /=.
rewrite pairmap_rcons foldr_rcons /=.
rewrite unzip1_rcons last_rcons /=.
set l := pairmap _ _ _.
induction l ; simpl.
apply plus_comm.
rewrite IHl.
Admitted.

Lemma Riemann_sum_zero (f : R -> V) ptd : SF_sorted Rle ptd -> SF_h ptd = last (SF_h ptd) (SF_lx ptd) -> Riemann_sum f ptd = zero.
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd IH] //= Hs Hhl.
rewrite Riemann_sum_cons IH /= => {IH}.
replace x0 with (SF_h ptd).
rewrite Rminus_eq_0.
rewrite plus_zero_r.
by apply: scal_zero_l.
apply Rle_antisym.
rewrite Hhl => {Hhl} /=.
apply (sorted_last (SF_h ptd :: @map (R*R) R (@fst R R) (SF_t ptd)) O) with (x0 := 0).
replace ((SF_h ptd) :: map _ _) with (SF_lx ptd).
apply Hs.
apply SF_cons_ind with (s := ptd) => {ptd Hs} [x1 | [x1 y1] ptd IH] //=.
apply lt_O_Sn.
apply Hs.
apply Hs.
apply Rle_antisym.
apply (sorted_last (SF_h ptd :: @map (R*R) R (@fst R R) (SF_t ptd)) O) with (x0 := 0).
replace ((SF_h ptd) :: map _ _) with (SF_lx ptd).
apply Hs.
apply SF_cons_ind with (s := ptd) => {ptd Hs Hhl} [x1 | [x1 y1] ptd IH] //=.
apply lt_O_Sn.
Admitted.

Lemma SF_ly_f1 {T : Type} (f1 : R -> T) P : SF_ly (SF_seq_f1 f1 P) = Rcomplements.belast (map f1 P).
Proof.
case: P => [| h P] // ; elim: P h => //= h P IH h0 ; by rewrite -(IH h).

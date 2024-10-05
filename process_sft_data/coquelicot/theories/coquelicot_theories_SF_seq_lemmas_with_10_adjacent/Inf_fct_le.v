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

Lemma ad_SF_val_fun (f : R -> R) (a b : R) (n : nat) : ((a <= b) -> adapted_couple (SF_val_fun f a b n) a b (seq2Rlist (unif_part a b n)) (seq2Rlist (SF_val_ly f a b n))) /\ (~(a <= b) -> adapted_couple (SF_val_fun f b a n) a b (seq2Rlist (unif_part b a n)) (seq2Rlist (SF_val_ly f b a n))).
Proof.
wlog : a b / (a <= b) => Hw.
split ; case: (Rle_dec a b) => // Hab _.
by apply Hw.
apply StepFun_P2 ; apply Hw ; by apply Rlt_le, Rnot_le_lt.
split ; case: (Rle_dec a b) => // {Hw} Hab _.
have : (a = head 0 (SF_lx (SF_val_seq f a b n))) ; [rewrite SF_lx_f2 /= ; (try by apply lt_O_Sn) ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
pattern b at 3 ; replace b with (last 0 (SF_lx (SF_val_seq f a b n))).
rewrite -(SF_lx_f2 (fun x y => f ((x+y)/2)) (unif_part a b n)) ; try by apply lt_O_Sn.
rewrite /SF_val_ly -SF_ly_f2.
unfold SF_val_fun, SF_fun_f2.
replace (SF_seq_f2 (fun x y : R => f ((x + y) / 2)) (unif_part a b n)) with (SF_val_seq f a b n) by auto.
apply (ad_SF_compat _ (SF_val_seq f a b n)).
by apply SF_sorted_f2, unif_part_sort.
rewrite SF_lx_f2 ; replace (head 0 (unif_part a b n) :: behead (unif_part a b n)) with (unif_part a b n) by auto.
rewrite -nth_last size_mkseq nth_mkseq ?S_INR //= ; field ; apply Rgt_not_eq, INRp1_pos.
Admitted.

Definition sf_SF_val_fun (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
case : (Rle_dec a b) => Hab.
exists (SF_val_fun f a b n) ; exists (seq2Rlist (unif_part a b n)) ; exists (seq2Rlist (SF_val_ly f a b n)) ; by apply ad_SF_val_fun.
Admitted.

Lemma SF_val_subdiv (f : R -> R) (a b : R) (n : nat) : subdivision (sf_SF_val_fun f a b n) = match (Rle_dec a b) with | left _ => seq2Rlist (unif_part a b n) | right _ => seq2Rlist (unif_part b a n) end.
Proof.
Admitted.

Lemma SF_val_subdiv_val (f : R -> R) (a b : R) (n : nat) : subdivision_val (sf_SF_val_fun f a b n) = match (Rle_dec a b) with | left _ => seq2Rlist (SF_val_ly f a b n) | right _ => seq2Rlist (SF_val_ly f b a n) end.
Proof.
Admitted.

Lemma SF_val_fun_rw (f : R -> R) (a b : R) (n : nat) (x : R) (Hx : a <= x <= b) : SF_val_fun f a b n x = match (unif_part_nat a b n x Hx) with | inleft H => f (a + (INR (proj1_sig H) + /2) * (b-a) / (INR n + 1)) | inright _ => f (a + (INR n + /2) * (b-a) / (INR n + 1)) end.
Proof.
have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
case: unif_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] /=.
rewrite /SF_val_fun /SF_fun_f2.
replace (a + (INR i + /2) * (b - a) / (INR n+1)) with ((nth 0 (unif_part a b n) i + nth 0 (unif_part a b n) (S i)) / 2) ; [ | rewrite size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ; [field ; apply Rgt_not_eq | apply SSR_leq | apply SSR_leq ] ; intuition].
case: (unif_part a b n) (unif_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
by apply lt_n_O in Hi.
case: (s) Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [| h0 s] Hs /= i Hi.
by apply lt_n_O in Hi.
elim: (s) h h0 Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [|h1 s IH] h h0 Hs /= i Hi x Hx.
by apply lt_n_O in Hi.
case: i Hx Hi => [|i]/= Hx Hi.
rewrite /SF_fun /=.
case: Rlt_dec => [Hx0 | _ ].
contradict Hx0 ; apply Rle_not_lt, Hx.
case: Rlt_dec => // Hx0 ; contradict Hx0 ; apply Hx.
rewrite -(IH h0 h1 (proj2 Hs) i (lt_S_n _ _ Hi) x Hx).
rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
case: Rlt_dec => [ Hx0 | _ ] //.
contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
replace (a + (INR n + /2) * (b - a) / (INR n + 1)) with ((nth 0 (unif_part a b n) (n) + nth 0 (unif_part a b n) (S n)) / 2) ; [ | rewrite ?nth_mkseq ?minus_INR ?S_INR /= ; [field ; apply Rgt_not_eq | apply SSR_leq | apply SSR_leq ] ; intuition].
suff : (1 < size (unif_part a b n))%nat.
move: x Hx ; have: (n = size (unif_part a b n) - 2)%nat ; [ rewrite size_mkseq ; intuition | ].
move => {2 4 8 10}->.
rewrite /SF_val_fun /SF_fun_f2.
case: (unif_part a b n) (unif_part_sort a b n Hab) => {a b Hab n} [| h s Hs x Hx /= Hi] .
intros _ x Hx Hi.
by apply lt_n_O in Hi.
case: s h Hs Hi x Hx => [| h0 s] h Hs /= Hi.
by apply lt_irrefl in Hi.
elim: s h h0 Hs {Hi} => [| h1 s IH] h h0 Hs /= x Hx.
rewrite /SF_fun /= ; case: Rlt_dec => [Hx0 | _].
contradict Hx0 ; apply Rle_not_lt, Hx.
case: Rle_dec => [| Hx0] // ; contradict Hx0 ; apply Hx.
rewrite -minus_n_O in IH.
rewrite -(IH h0 h1 (proj2 Hs) x Hx ).
rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
case: Rlt_dec => [ Hx0 | _ ] //.
contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
Admitted.

Lemma RInt_val_Reals (f : R -> R) (a b : R) (n : nat) : RInt_val f a b n = RiemannInt_SF (sf_SF_val_fun f a b n).
Proof.
rewrite /RiemannInt_SF SF_val_subdiv SF_val_subdiv_val ; case: Rle_dec => Hab.
rewrite /RInt_val /SF_val_ly ; case: (unif_part a b n) => [| h s] /=.
by [].
elim: s h => [|h0 s IH] h /=.
by [].
rewrite (SF_cons_f2 _ h).
2: by apply lt_O_Sn.
rewrite Riemann_sum_cons /= IH /plus /scal /= /mult /=.
ring.
rewrite RInt_val_swap /SF_val_ly /RInt_val.
simpl opp ; apply f_equal.
case: (unif_part b a n) => [| h s] /=.
by [].
elim: s h => [|h0 s IH] h /=.
by [].
rewrite SF_cons_f2.
2: by apply lt_O_Sn.
rewrite Riemann_sum_cons IH /= /plus /scal /= /mult /=.
Admitted.

Lemma ex_Im_fct (f : R -> R) (a b : R) : a <> b -> exists x, (fun y => exists x, y = f x /\ Rmin a b < x < Rmax a b) x.
Proof.
exists (f ((a+b)/2)) ; exists ((a+b)/2) ; split.
by [].
rewrite /Rmin /Rmax.
Admitted.

Lemma Sup_fct_bound (f : R -> R) (a b : R) : Sup_fct f a b = Sup_fct f b a.
Proof.
rewrite /Sup_fct /= ; case: Req_EM_T => Hab ; case: Req_EM_T => Hba.
by [].
by apply sym_equal in Hab.
by apply sym_equal in Hba.
Admitted.

Lemma Inf_fct_bound (f : R -> R) (a b : R) : Inf_fct f a b = Inf_fct f b a.
Proof.
rewrite /Inf_fct /= ; case: Req_EM_T => Hab ; case: Req_EM_T => Hba.
by [].
by apply sym_equal in Hab.
by apply sym_equal in Hba.
Admitted.

Lemma Sup_fct_le (f : R -> R) (a b : R) (x : R) : (Rmin a b < x < Rmax a b) -> Rbar_le (Finite (f x)) (Sup_fct f a b).
Proof.
move => Hx ; rewrite /Sup_fct.
case: Req_EM_T => Hab.
move: (Rlt_trans _ _ _ (proj1 Hx) (proj2 Hx)) => {Hx} ; rewrite /Rmin /Rmax ; case: Rle_dec (Req_le _ _ Hab) => //= _ _ Hx.
contradict Hx ; by apply Rle_not_lt, Req_le.
Admitted.

Lemma Sup_fct_maj (f : R -> R) (a b : R) (M : R) : (forall x, Rmin a b < x < Rmax a b -> f x <= M) -> is_finite (Sup_fct f a b).
Proof.
rewrite /Sup_fct ; case: Req_EM_T => Hab Hf.
by [].
rewrite /Lub_Rbar ; case: ex_lub_Rbar ; case => [l | | ] [lub ub] /=.
by [].
case: (ub (Finite M)) => //.
move => _ [x [-> Hx]].
by apply Hf.
case: (lub (f((a+b)/2))) => //.
exists ((a + b) / 2) ; split.
by [].
rewrite /Rmin /Rmax.
Admitted.

Lemma Inf_fct_min (f : R -> R) (a b : R) (m : R) : (forall x, Rmin a b < x < Rmax a b -> m <= f x) -> is_finite (Inf_fct f a b).
Proof.
rewrite /Inf_fct ; case: Req_EM_T => Hab Hf.
by [].
rewrite /Glb_Rbar ; case: ex_glb_Rbar ; case => [l | | ] [lub ub] /=.
by [].
case: (lub (f((a+b)/2))) => //.
exists ((a + b) / 2) ; split.
by [].
rewrite /Rmin /Rmax.
case Rle_dec ; lra.
case: (ub (Finite m)) => //.
move => _ [x [-> Hx]].
Admitted.

Lemma SF_sup_lx (f : R -> R) (a b : R) (n : nat) : SF_lx (SF_sup_seq f a b n) = unif_part a b n.
Proof.
apply SF_lx_f2.
Admitted.

Lemma SF_sup_ly (f : R -> R) (a b : R) (n : nat) : SF_ly (SF_sup_seq f a b n) = behead (pairmap (Sup_fct f) 0 (unif_part a b n)).
Proof.
Admitted.

Lemma SF_inf_lx (f : R -> R) (a b : R) (n : nat) : SF_lx (SF_inf_seq f a b n) = unif_part a b n.
Proof.
Admitted.

Lemma SF_inf_ly (f : R -> R) (a b : R) (n : nat) : SF_ly (SF_inf_seq f a b n) = behead (pairmap (Inf_fct f) 0 (unif_part a b n)).
Proof.
Admitted.

Lemma SF_sup_bound (f : R -> R) (a b : R) (n : nat) : SF_rev (SF_sup_seq f a b n) = SF_sup_seq f b a n.
Proof.
rewrite /SF_sup_seq unif_part_bound => //.
rewrite SF_rev_f2 ?revK //.
Admitted.

Lemma SF_inf_bound (f : R -> R) (a b : R) (n : nat) : SF_rev (SF_inf_seq f a b n) = SF_inf_seq f b a n.
Proof.
rewrite /SF_inf_seq unif_part_bound => //.
rewrite SF_rev_f2 ?revK //.
Admitted.

Lemma SF_sup_fun_bound (f : R -> R) (a b : R) (n : nat) (x : R) : SF_sup_fun f a b n x = SF_sup_fun f b a n x.
Proof.
rewrite /SF_sup_fun ; case: (Rle_dec a b) => Hab ; case : (Rle_dec b a) => Hba //.
by rewrite (Rle_antisym _ _ Hab Hba).
Admitted.

Lemma SF_inf_fun_bound (f : R -> R) (a b : R) (n : nat) (x : R) : SF_inf_fun f a b n x = SF_inf_fun f b a n x.
Proof.
rewrite /SF_inf_fun ; case: (Rle_dec a b) => Hab ; case : (Rle_dec b a) => Hba //.
by rewrite (Rle_antisym _ _ Hab Hba).
Admitted.

Lemma Inf_fct_le (f : R -> R) (a b : R) (x : R) : (Rmin a b < x < Rmax a b) -> Rbar_le (Inf_fct f a b) (Finite (f x)).
Proof.
move => Hx ; rewrite /Inf_fct.
case: Req_EM_T => Hab.
move: (Rlt_trans _ _ _ (proj1 Hx) (proj2 Hx)) => {Hx} ; rewrite /Rmin /Rmax ; case: Rle_dec (Req_le _ _ Hab) => //= _ _ Hx.
contradict Hx ; by apply Rle_not_lt, Req_le.
rewrite /Glb_Rbar ; case: ex_glb_Rbar => l lub ; apply lub ; exists x ; split ; by [].

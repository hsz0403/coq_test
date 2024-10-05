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

Lemma SF_ly_f1 {T : Type} (f1 : R -> T) P : SF_ly (SF_seq_f1 f1 P) = Rcomplements.belast (map f1 P).
Proof.
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

Lemma Riemann_sum_map (f : R -> V) (g : R -> R) ptd : Riemann_sum (fun x => f (g x)) ptd = Riemann_sum f (SF_map g ptd).
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | h ptd IH].
by [].
rewrite SF_map_cons !Riemann_sum_cons /=.
Admitted.

Lemma Riemann_sum_const (v : V) ptd : Riemann_sum (fun _ => v) ptd = scal (last (SF_h ptd) (SF_lx ptd) - SF_h ptd) v.
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] s IH] /=.
by rewrite /Riemann_sum /= Rminus_eq_0 scal_zero_l.
rewrite Riemann_sum_cons IH /=.
rewrite -scal_distr_r /=.
apply (f_equal (fun x => scal x v)).
rewrite /plus /=.
Admitted.

Lemma Riemann_sum_scal (a : R) (f : R -> V) ptd : Riemann_sum (fun x => scal a (f x)) ptd = scal a (Riemann_sum f ptd).
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH].
rewrite /Riemann_sum /=.
apply sym_eq.
apply @scal_zero_r.
rewrite !Riemann_sum_cons /= IH.
rewrite scal_distr_l.
apply f_equal with (f := fun v => plus v _).
rewrite 2!scal_assoc.
Admitted.

Lemma Riemann_sum_opp (f : R -> V) ptd : Riemann_sum (fun x => opp (f x)) ptd = opp (Riemann_sum f ptd).
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH].
rewrite /Riemann_sum /=.
apply sym_eq, @opp_zero.
rewrite !Riemann_sum_cons /= IH.
rewrite opp_plus.
apply f_equal with (f := fun v => plus v (opp (Riemann_sum f s))).
Admitted.

Lemma Riemann_sum_plus (f g : R -> V) ptd : Riemann_sum (fun x => plus (f x) (g x)) ptd = plus (Riemann_sum f ptd) (Riemann_sum g ptd).
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH].
rewrite /Riemann_sum /=.
apply sym_eq, @plus_zero_l.
rewrite !Riemann_sum_cons /= ; rewrite IH.
rewrite scal_distr_l.
rewrite -!plus_assoc.
apply f_equal.
rewrite !plus_assoc.
apply (f_equal (fun x => plus x (Riemann_sum g s))).
Admitted.

Lemma Riemann_sum_minus (f g : R -> V) ptd : Riemann_sum (fun x => minus (f x) (g x)) ptd = minus (Riemann_sum f ptd) (Riemann_sum g ptd).
Proof.
unfold minus.
rewrite -Riemann_sum_opp.
Admitted.

Lemma Riemann_sum_Chasles_0 (f : R -> V) (M : R) (x : R) ptd : forall (eps : posreal), (forall x, SF_h ptd <= x <= last (SF_h ptd) (SF_lx ptd) -> norm (f x) < M) -> SF_h ptd <= x <= last (SF_h ptd) (SF_lx ptd) -> pointed_subdiv ptd -> seq_step (SF_lx ptd) < eps -> norm (minus (plus (Riemann_sum f (SF_cut_down ptd x)) (Riemann_sum f (SF_cut_up ptd x))) (Riemann_sum f ptd)) < 2 * eps * M.
Proof.
intros eps.
apply (SF_cons_ind (T := R)) with (s := ptd) => {ptd} /= [ x0 | [x0 y1] ptd IH] /= Hfx [ Hx0 Hl] Hptd Hstep.
+
rewrite (Rle_antisym _ _ Hx0 Hl) ; clear -Hfx.
rewrite /Riemann_sum /=.
case: Rle_dec (Rle_refl x) => //= _ _.
rewrite ?plus_zero_r Rminus_eq_0.
rewrite scal_zero_l.
rewrite /minus plus_zero_l norm_opp norm_zero.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
by apply Rlt_0_2.
by apply eps.
by apply Rle_lt_trans with (2:= (Hfx x0 (conj (Rle_refl _) (Rle_refl _)))), norm_ge_0.
+
case: (Rle_dec (SF_h ptd) x) => Hx1.
-
replace (minus (plus (Riemann_sum f (SF_cut_down (SF_cons (x0, y1) ptd) x)) (Riemann_sum f (SF_cut_up (SF_cons (x0, y1) ptd) x))) (Riemann_sum f (SF_cons (x0, y1) ptd))) with (minus (plus (Riemann_sum f (SF_cut_down ptd x)) (Riemann_sum f (SF_cut_up ptd x))) (Riemann_sum f ptd)).
apply IH.
intros y Hy.
apply Hfx.
split.
apply Rle_trans with y1.
by apply (Hptd O (lt_O_Sn _)).
apply Rle_trans with (SF_h ptd).
by apply (Hptd O (lt_O_Sn _)).
by apply Hy.
by apply Hy.
by split.
by apply ptd_cons in Hptd.
apply Rle_lt_trans with (2 := Hstep).
by apply Rmax_r.
rewrite SF_cut_down_cons_2.
rewrite SF_cut_up_cons_2.
rewrite /minus 2?(Riemann_sum_cons _ (x0, y1)) SF_cut_down_h.
rewrite opp_plus plus_assoc /=.
apply (f_equal (fun x => plus x _)).
rewrite (plus_comm (scal (SF_h ptd - x0) (f y1))) -2!plus_assoc.
apply f_equal.
by rewrite plus_comm -plus_assoc plus_opp_l plus_zero_r.
by [].
split ; [ | apply Hx1].
apply Rle_trans with y1 ; by apply (Hptd O (lt_O_Sn _)).
split ; [ | apply Hx1].
apply Rle_trans with y1 ; by apply (Hptd O (lt_O_Sn _)).
-
apply Rnot_le_lt in Hx1.
rewrite SF_cut_down_cons_1 /=.
rewrite SF_cut_up_cons_1 /=.
rewrite 3!Riemann_sum_cons /= => {IH}.
replace (Riemann_sum f (SF_nil x) : V) with (zero : V) by auto.
rewrite plus_zero_r /minus opp_plus.
rewrite (plus_comm (opp (scal (SF_h ptd - x0) (f y1)))).
rewrite ?plus_assoc -(plus_assoc _ _ (opp (Riemann_sum f ptd))).
rewrite plus_opp_r plus_zero_r.
rewrite -scal_opp_l.
rewrite /opp /= Ropp_minus_distr.
rewrite /Rmin /Rmax ; case: Rle_dec => _.
rewrite (plus_comm (scal (x - x0) (f y1))) -plus_assoc.
rewrite -scal_distr_r /plus /= -/plus.
ring_simplify (x - x0 + (x0 - SF_h ptd)).
eapply Rle_lt_trans.
apply @norm_triangle.
replace (2 * eps * M) with (eps * M + eps * M) by ring.
apply Rplus_lt_compat ; eapply Rle_lt_trans ; try (apply @norm_scal) ; apply Rmult_le_0_lt_compat.
by apply Rabs_pos.
by apply norm_ge_0.
apply Rle_lt_trans with (2 := Hstep).
apply Rle_trans with (2 := Rmax_l _ _).
simpl.
apply Rlt_le in Hx1.
move: (Rle_trans _ _ _ Hx0 Hx1) => Hx0'.
apply Rminus_le_0 in Hx1.
apply Rminus_le_0 in Hx0'.
rewrite /abs /= ?Rabs_pos_eq //.
by apply Rplus_le_compat_l, Ropp_le_contravar.
apply Hfx.
by split.
by apply Rabs_pos.
by apply norm_ge_0.
apply Rle_lt_trans with (2 := Hstep).
apply Rle_trans with (2 := Rmax_l _ _).
rewrite /abs /plus /= -Ropp_minus_distr Rabs_Ropp.
apply Rlt_le in Hx1.
move: (Rle_trans _ _ _ Hx0 Hx1) => Hx0'.
apply Rminus_le_0 in Hx1.
apply Rminus_le_0 in Hx0'.
rewrite ?Rabs_pos_eq //.
by apply Rplus_le_compat_l, Ropp_le_contravar.
apply Hfx.
split.
apply (Hptd O (lt_O_Sn _)).
apply Rle_trans with (SF_h ptd).
apply (Hptd O (lt_O_Sn _)).
apply (fun H => sorted_last ((SF_h ptd) :: (unzip1 (SF_t ptd))) O H (lt_O_Sn _) (SF_h ptd)).
apply ptd_sort in Hptd.
by apply Hptd.
rewrite -plus_assoc -scal_distr_r /plus /= -/plus.
replace (SF_h ptd - x + (x0 - SF_h ptd)) with (opp (x - x0)) by (rewrite /opp /= ; ring).
rewrite scal_opp_l -scal_opp_r.
rewrite -scal_distr_l.
eapply Rle_lt_trans.
apply @norm_scal.
replace (2 * eps * M) with (eps * (M + M)) by ring.
apply Rmult_le_0_lt_compat.
by apply Rabs_pos.
by apply norm_ge_0.
apply Rle_lt_trans with (2 := Hstep).
apply Rle_trans with (2 := Rmax_l _ _).
simpl.
apply Rlt_le in Hx1.
move: (Rle_trans _ _ _ Hx0 Hx1) => Hx0'.
apply Rminus_le_0 in Hx0.
apply Rminus_le_0 in Hx0'.
rewrite /abs /= ?Rabs_pos_eq //.
by apply Rplus_le_compat_r.
apply Rle_lt_trans with (norm (f x) + norm (opp (f y1))).
apply @norm_triangle.
apply Rplus_lt_compat.
apply Hfx.
by split.
rewrite norm_opp.
apply Hfx.
split.
apply (Hptd O (lt_O_Sn _)).
apply Rle_trans with (SF_h ptd).
apply (Hptd O (lt_O_Sn _)).
apply (fun H => sorted_last ((SF_h ptd) :: (unzip1 (SF_t ptd))) O H (lt_O_Sn _) (SF_h ptd)).
apply ptd_sort in Hptd.
by apply Hptd.
by split.
Admitted.

Lemma Riemann_sum_norm (f : R -> V) (g : R -> R) ptd : pointed_subdiv ptd -> (forall t, SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> norm (f t) <= g t) -> norm (Riemann_sum f ptd) <= Riemann_sum g ptd.
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH] /= Hs H.
rewrite norm_zero ; exact: Rle_refl.
rewrite !Riemann_sum_cons /=.
eapply Rle_trans.
by apply @norm_triangle.
apply Rplus_le_compat.
eapply Rle_trans.
apply @norm_scal.
refine (_ (Hs O _)).
simpl.
intros [H1 H2].
rewrite /abs /= Rabs_pos_eq.
apply Rmult_le_compat_l.
apply -> Rminus_le_0.
now apply Rle_trans with y0.
apply H.
apply (conj H1).
apply Rle_trans with (1 := H2).
apply (sorted_last (SF_lx s) O) with (x0 := 0).
by apply (ptd_sort _ Hs).
exact: lt_O_Sn.
apply -> Rminus_le_0.
now apply Rle_trans with y0.
exact: lt_O_Sn.
apply IH.
by apply ptd_cons with (h := (x0,y0)).
move => t Ht ; apply H ; split.
by apply Rle_trans with (2 := proj1 Ht), (ptd_sort _ Hs).
Admitted.

Lemma Riemann_sum_le (f : R -> R) (g : R -> R) ptd : pointed_subdiv ptd -> (forall t, SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> f t <= g t) -> Riemann_sum f ptd <= Riemann_sum g ptd.
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH] /= Hs H.
apply Rle_refl.
rewrite !Riemann_sum_cons /=.
apply Rplus_le_compat.
refine (_ (Hs O _)).
simpl.
intros [H1 H2].
apply Rmult_le_compat_l.
apply -> Rminus_le_0.
now apply Rle_trans with y0.
apply H.
apply (conj H1).
apply Rle_trans with (1 := H2).
apply (sorted_last (SF_lx s) O) with (x0 := 0).
by apply (ptd_sort _ Hs).
exact: lt_O_Sn.
exact: lt_O_Sn.
apply IH.
by apply ptd_cons with (h := (x0,y0)).
move => t Ht ; apply H ; split.
by apply Rle_trans with (2 := proj1 Ht), (ptd_sort _ Hs).
Admitted.

Lemma Riemann_sum_pair {U : ModuleSpace R_Ring} {V : ModuleSpace R_Ring} (f : R -> U * V) ptd : Riemann_sum f ptd = (Riemann_sum (fun t => fst (f t)) ptd, Riemann_sum (fun t => snd (f t)) ptd).
Proof.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | h0 ptd IH].
by [].
rewrite !Riemann_sum_cons IH.
Admitted.

Lemma RInt_val_point (f : R -> V) (a : R) (n : nat) : RInt_val f a a n = zero.
Proof.
unfold RInt_val ; apply Riemann_sum_zero.
rewrite /SF_sorted SF_lx_f2.
apply unif_part_sort ; apply Rle_refl.
rewrite size_mkseq ; by apply lt_O_Sn.
rewrite SF_lx_f2 /=.
rewrite -{2}[1]/(INR 1) last_map.
unfold Rdiv ; ring.
Admitted.

Lemma RInt_val_swap : forall (f : R -> V) (a b : R) (n : nat), RInt_val f a b n = opp (RInt_val f b a n).
Proof.
intros f a b n.
rewrite /RInt_val.
rewrite -Riemann_sum_opp.
rewrite unif_part_bound.
elim: (unif_part b a n) => [ | x1 s IH] /=.
by [].
clear -IH.
rewrite rev_cons.
destruct s as [ | x2 s].
by [].
rewrite SF_cons_f2.
2: by apply lt_O_Sn.
rewrite Riemann_sum_cons /= -IH => {IH}.
rewrite scal_opp_r -scal_opp_l /=.
rewrite rev_cons.
elim: (rev s) => {s} /= [ | x3 s IH].
rewrite /Riemann_sum /=.
apply (f_equal2 (fun x y => plus (scal x (f y)) _)) ; rewrite /Rdiv /opp /= ; ring.
rewrite !SF_cons_f2 ; try (by rewrite size_rcons ; apply lt_O_Sn).
rewrite !Riemann_sum_cons /= IH !plus_assoc => {IH}.
apply (f_equal (fun x => plus x _)).
rewrite plus_comm.
apply f_equal.
Admitted.

Lemma RInt_val_ext (f g : R -> V) (a b : R) (n : nat) : (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) -> RInt_val g a b n = RInt_val f a b n.
Proof.
wlog: a b / (a <= b) => [Hw | Hab].
case: (Rle_lt_dec a b) => Hab.
by apply Hw.
rewrite Rmin_comm Rmax_comm => Heq.
apply Rlt_le in Hab.
rewrite RInt_val_swap Hw => //=.
apply sym_eq ; by apply RInt_val_swap.
rewrite /Rmin /Rmax ; case: Rle_dec => //= _ Heq.
unfold RInt_val.
set l := (SF_seq_f2 (fun x y : R => (x + y) / 2) (unif_part a b n)).
assert (forall i, (i < size (SF_ly l))%nat -> f (nth 0 (SF_ly l) i) = g (nth 0 (SF_ly l) i)).
move => i Hi.
apply Heq.
destruct (fun H0 => Riemann_fine_unif_part (fun x y : R => (x + y) / 2) a b n H0 Hab) as [H [H0 [H1 H2]]].
clear.
intros a b Hab.
lra.
fold l in H, H0, H1, H2.
rewrite -H1 -H2 ; split.
apply Rle_trans with (head 0 (SF_ly l)).
apply (H0 O).
by apply lt_O_Sn.
apply sorted_head.
by apply ptd_sort'.
by [].
apply Rle_trans with (last 0 (SF_ly l)).
apply sorted_last.
by apply ptd_sort'.
by [].
rewrite -!nth_last SF_size_ly SF_size_lx SF_size_f2 size_mkseq.
simpl Peano.pred.
replace (nth (SF_h l) (SF_lx l) (S n)) with (nth 0 (SF_lx l) (S n)).
apply (H0 n).
rewrite SF_size_f2 size_mkseq /=.
by apply lt_n_Sn.
rewrite SF_lx_f2.
assert (size (unif_part a b n) = S (S n)).
by apply size_mkseq.
elim: (S n) (unif_part a b n) H3 ; simpl ; clear ; intros.
destruct unif_part0 ; simpl => //.
replace unif_part0 with (head 0 unif_part0 :: behead unif_part0).
apply H.
destruct unif_part0 ; by intuition.
destruct unif_part0 ; by intuition.
by apply lt_O_Sn.
move: H => {Heq}.
apply SF_cons_ind with (s := l) => {l} [x0 | h0 s IH] /= Heq.
by [].
rewrite !Riemann_sum_cons.
apply (f_equal2 (fun x y => plus (scal (SF_h s - fst h0) x) y)).
by apply sym_eq, (Heq O), lt_O_Sn.
apply IH => i Hi.
Admitted.

Lemma RInt_val_comp_opp (f : R -> V) (a b : R) (n : nat) : RInt_val (fun x => f (- x)) a b n = opp (RInt_val f (- a) (- b) n).
Proof.
rewrite /RInt_val.
replace (unif_part (- a) (- b) n) with (map Ropp (unif_part a b n)).
elim: (unif_part a b n) {1}0 {2}0 => /= [ | x1 s IH] x0 x0'.
rewrite /Riemann_sum /=.
by apply sym_eq, @opp_zero.
destruct s as [ | x2 s].
rewrite /Riemann_sum /=.
by apply sym_eq, @opp_zero.
rewrite (SF_cons_f2 _ x1) ; try by apply lt_O_Sn.
rewrite (SF_cons_f2 _ (- x1)) ; try by apply lt_O_Sn.
rewrite !Riemann_sum_cons /=.
rewrite opp_plus.
apply f_equal2.
rewrite -scal_opp_l.
apply (f_equal2 (fun x y => scal x (f y))) ; rewrite /Rdiv /opp /= ; field.
by apply IH.
apply eq_from_nth with 0.
by rewrite size_map !size_mkseq.
rewrite size_map => i Hi.
rewrite (nth_map 0 0) => //.
rewrite size_mkseq in Hi.
rewrite !nth_mkseq => //.
field.
Admitted.

Lemma RInt_val_comp_lin (f : R -> V) (u v : R) (a b : R) (n : nat) : scal u (RInt_val (fun x => f (u * x + v)) a b n) = RInt_val f (u * a + v) (u * b + v) n.
Proof.
rewrite /RInt_val.
replace (unif_part (u * a + v) (u * b + v) n) with (map (fun x => u * x + v) (unif_part a b n)).
elim: (unif_part a b n) {1}0 {2}0 => /= [ | x1 s IH] x0 x0'.
by apply @scal_zero_r.
destruct s as [ | x2 s].
by apply @scal_zero_r.
rewrite (SF_cons_f2 _ x1) ; try by apply lt_O_Sn.
rewrite (SF_cons_f2 _ (u * x1 + v)) ; try by apply lt_O_Sn.
rewrite !Riemann_sum_cons /=.
rewrite scal_distr_l.
apply f_equal2.
rewrite scal_assoc.
apply (f_equal2 (fun x y => scal x (f y))) ; rewrite /mult /= ; field.
by apply IH.
apply eq_from_nth with 0.
by rewrite size_map !size_mkseq.
rewrite size_map => i Hi.
rewrite (nth_map 0 0) => //.
rewrite size_mkseq in Hi.
rewrite !nth_mkseq => //.
field.
Admitted.

Lemma SF_Chasles {V : ModuleSpace R_AbsRing} (f : R -> V) (s : SF_seq) x x0 : (SF_h s <= x <= last (SF_h s) (unzip1 (SF_t s))) -> Riemann_sum f s = plus (Riemann_sum f (SF_cut_down' s x x0)) (Riemann_sum f (SF_cut_up' s x x0)).
Proof.
rename x0 into z0.
apply SF_cons_ind with (s := s) => {s} /= [ x0 | [x0 y0] s IH] /= Hx.
rewrite (Rle_antisym _ _ (proj1 Hx) (proj2 Hx)).
move: (Rle_refl x).
rewrite /SF_cut_down' /SF_cut_up' /= ; case: Rle_dec => //= _ _.
by rewrite /Riemann_sum /= Rminus_eq_0 scal_zero_l !plus_zero_l.
move: (fun Hx1 => IH (conj Hx1 (proj2 Hx))) => {IH}.
rewrite /SF_cut_down' /SF_cut_up' /= ; case: (Rle_dec x0 _) (proj1 Hx) => //= Hx0 _.
case: (Rle_dec (SF_h s) x) => //= Hx1 IH.
move: (IH Hx1) => {IH} IH.
rewrite (Riemann_sum_cons _ (x0,y0)) (Riemann_sum_cons _ (x0,y0) (mkSF_seq (SF_h s) (seq_cut_down' (SF_t s) x y0))) IH /= => {IH}.
rewrite -!plus_assoc ; apply f_equal.
assert (forall x0 y0, fst (head (x0, z0) (seq_cut_up' (SF_t s) x y0)) = x).
elim: (SF_t s) => [ | x2 t IH] x1 y1 //=.
by case: Rle_dec.
rewrite ?H.
move: (proj2 Hx) Hx1 => {Hx} ; apply SF_cons_dec with (s := s) => {s H} /= [x1 | [x1 y1] s] //= Hx Hx1.
by rewrite /Riemann_sum /= (Rle_antisym _ _ Hx Hx1) Rminus_eq_0 !scal_zero_l !plus_zero_l.
case: Rle_dec => //.
rewrite Riemann_sum_cons (Riemann_sum_cons _ (x,y0) s) {2}/Riemann_sum /=.
clear IH.
rewrite plus_zero_r !plus_assoc.
apply f_equal2 => //.
rewrite -scal_distr_r.
apply f_equal2 => //.
Admitted.

Lemma seq_cut_up_head' (s : seq (R*R)) x x0 z : fst (head z (seq_cut_up' s x x0)) = x.
Proof.
elim: s z x0 => [ | x1 s IH] //= z x0.
Admitted.

Lemma ad_SF_compat z0 (s : SF_seq) (pr : SF_sorted Rle s) : adapted_couple (SF_fun s z0) (head 0 (SF_lx s)) (last 0 (SF_lx s)) (seq2Rlist (SF_lx s)) (seq2Rlist (SF_ly s)).
Proof.
have H : ((head 0 (SF_lx s)) <= (last 0 (SF_lx s))).
move: pr ; rewrite /SF_sorted.
case: (SF_lx s) => {s} [| h s] Hs.
apply Rle_refl.
rewrite -nth0 ; apply sorted_last => // ; apply lt_O_Sn.
rewrite /adapted_couple ?nth_compat ?size_compat ?nth0 ?nth_last /Rmin /Rmax ?SF_size_lx ?SF_size_ly ; case: (Rle_dec (head 0 (SF_lx s)) (last 0 (SF_lx s))) => // {H} _ ; intuition.
apply sorted_compat => //.
move: i pr H ; apply SF_cons_dec with (s := s) => {s} [x0 | h s] i Hs Hi x [Hx0 Hx1].
by apply lt_n_O in Hi.
rewrite /SF_fun ?SF_size_cons ?nth_compat -?SF_size_lx ?SF_lx_cons in Hi, Hx0, Hx1 |- *.
simpl.
move: h i x {1}z0 Hs Hi Hx0 Hx1 ; apply SF_cons_ind with (s := s) => {s} [x1 | h0 s IH] h ; case => [| i ] x z0' Hs Hi Hx0 Hx1 //= ; case: Rlt_dec => Hx' //.
now contradict Hx' ; apply Rle_not_lt, Rlt_le, Hx0.
now case: Rle_dec => Hx'' // ; contradict Hx'' ; apply Rlt_le, Hx1.
now rewrite /= in Hi ; by apply lt_S_n, lt_n_O in Hi.
now rewrite /= in Hi ; by apply lt_S_n, lt_n_O in Hi.
now contradict Hx' ; apply Rle_not_lt, Rlt_le, Hx0.
now case: Rlt_dec => Hx'' //.
now contradict Hx' ; apply Rle_not_lt, Rlt_le, Rle_lt_trans with (2 := Hx0) ; have Hi' : (S i < size (SF_lx (SF_cons h (SF_cons h0 s))))%nat ; [ rewrite ?SF_lx_cons /= in Hi |-* ; apply lt_trans with (1 := Hi), lt_n_Sn | ] ; apply (sorted_head (SF_lx (SF_cons h (SF_cons h0 s))) (S i) Hs Hi' 0).
rewrite -(IH h0 i x (snd h)) //=.
apply Hs.
Admitted.

Lemma Riemann_sum_cons (f : R -> V) (h0 : R * R) (ptd : SF_seq) : Riemann_sum f (SF_cons h0 ptd) = plus (scal (SF_h ptd - fst h0) (f (snd h0))) (Riemann_sum f ptd).
Proof.
rewrite /Riemann_sum /=.
case: h0 => x0 y0 ; apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd ] //=.

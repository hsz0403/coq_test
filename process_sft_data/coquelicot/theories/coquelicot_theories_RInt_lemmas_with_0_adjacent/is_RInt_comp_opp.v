Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq SF_seq.
Require Import Continuity Hierarchy.
Section is_RInt.
Context {V : NormedModule R_AbsRing}.
Definition is_RInt (f : R -> V) (a b : R) (If : V) := filterlim (fun ptd => scal (sign (b-a)) (Riemann_sum f ptd)) (Riemann_fine a b) (locally If).
Definition ex_RInt (f : R -> V) (a b : R) := exists If : V, is_RInt f a b If.
End is_RInt.
Section StepFun.
Context {V : NormedModule R_AbsRing}.
End StepFun.
Section norm_RInt.
Context {V : NormedModule R_AbsRing}.
End norm_RInt.
Section prod.
Context {U V : NormedModule R_AbsRing}.
End prod.
Section RInt.
Context {V : CompleteNormedModule R_AbsRing}.
Definition RInt (f : R -> V) (a b : R) := iota (is_RInt f a b).
End RInt.

Lemma is_RInt_comp_opp : forall (f : R -> V) (a b : R) (l : V), is_RInt f (-a) (-b) l -> is_RInt (fun y => opp (f (- y))) a b l.
Proof.
intros f a b l Hf.
apply filterlim_locally => eps.
generalize (proj1 (filterlim_locally _ _) Hf eps) ; clear Hf ; intros [delta Hf].
exists delta.
intros ptd Hstep [Hptd [Hh Hl]].
rewrite Riemann_sum_opp.
rewrite scal_opp_r -scal_opp_l /opp /= -sign_opp.
rewrite Ropp_plus_distr.
set ptd' := (mkSF_seq (-SF_h ptd) (seq.map (fun X => (- fst X,- snd X)) (SF_t ptd))).
replace (Riemann_sum (fun x => f (-x)) ptd) with (Riemann_sum f (SF_rev ptd')).
have H : SF_size ptd = SF_size ptd'.
rewrite /SF_size /=.
by rewrite size_map.
apply Hf.
clear H ; revert ptd' Hstep ; apply SF_cons_dec with (s := ptd) => [ x0 s' Hs'| h0 s] ; rewrite /seq_step.
apply cond_pos.
set s' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
rewrite (SF_rev_cons (-fst h0,-snd h0) s').
rewrite SF_lx_rcons.
rewrite behead_rcons ; [ | rewrite SF_size_lx ; by apply lt_O_Sn ].
rewrite head_rcons.
rewrite SF_lx_cons.
revert h0 s' ; move: {1 3}(0) ; apply SF_cons_ind with (s := s) => {s} [ x1 | h1 s IH] x0 h0 s' Hs' ; simpl in Hs'.
rewrite /= -Ropp_minus_distr' /Rminus -Ropp_plus_distr Ropp_involutive.
by apply Hs'.
set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
rewrite (SF_rev_cons (-fst h1,-snd h1) s'').
rewrite SF_lx_rcons.
rewrite behead_rcons ; [ | rewrite SF_size_lx ; by apply lt_O_Sn ].
rewrite head_rcons.
rewrite pairmap_rcons.
rewrite foldr_rcons.
apply: IH => /=.
replace (Rmax (Rabs (SF_h s - fst h1)) (foldr Rmax (Rmax (Rabs (- fst h0 - - fst h1)) x0) (pairmap (fun x y : R => Rabs (y - x)) (SF_h s) (unzip1 (SF_t s))))) with (Rmax (Rabs (fst h1 - fst h0)) (Rmax (Rabs (SF_h s - fst h1)) (foldr Rmax x0 (pairmap (fun x y : R => Rabs (y - x)) (SF_h s) (unzip1 (SF_t s)))))).
by [].
rewrite Rmax_assoc (Rmax_comm (Rabs _)) -Rmax_assoc.
apply f_equal.
rewrite -(Ropp_minus_distr' (-fst h0)) /Rminus -Ropp_plus_distr Ropp_involutive.
elim: (pairmap (fun x y : R => Rabs (y + - x)) (SF_h s) (unzip1 (SF_t s))) x0 {Hs'} (Rabs (fst h1 + - fst h0)) => [ | x2 t IH] x0 x1 /=.
by [].
rewrite Rmax_assoc (Rmax_comm x1) -Rmax_assoc.
apply f_equal.
by apply IH.
split.
revert ptd' Hptd H ; apply SF_cons_ind with (s := ptd) => [ x0 | h0 s IH] s' Hs' H i Hi ; rewrite SF_size_rev -H in Hi.
by apply lt_n_O in Hi.
rewrite SF_size_cons in Hi.
apply lt_n_Sm_le in Hi.
set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
rewrite (SF_rev_cons (-fst h0,-snd h0) s'').
rewrite SF_size_cons (SF_size_cons (-fst h0,-snd h0) s'') in H.
apply eq_add_S in H.
rewrite SF_lx_rcons SF_ly_rcons.
rewrite ?nth_rcons.
rewrite ?SF_size_lx ?SF_size_ly ?SF_size_rev -H.
move: (proj2 (SSR_leq _ _) (le_n_S _ _ Hi)) ; case: (ssrnat.leq (S i) (S (SF_size s))) => // _.
apply le_lt_eq_dec in Hi ; case: Hi => [Hi | -> {i}].
apply lt_le_S in Hi.
move: (proj2 (SSR_leq _ _) Hi) ; case: (ssrnat.leq (S i) (SF_size s)) => // _.
move: (proj2 (SSR_leq _ _) (le_n_S _ _ Hi)) ; case: (ssrnat.leq (S (S i)) (S (SF_size s))) => // _.
apply IH.
move: Hs' ; apply ptd_cons.
apply H.
rewrite SF_size_rev -H.
intuition.
have : ~ is_true (ssrnat.leq (S (SF_size s)) (SF_size s)).
have H0 := lt_n_Sn (SF_size s).
contradict H0.
apply SSR_leq in H0.
by apply le_not_lt.
case: (ssrnat.leq (S (SF_size s)) (SF_size s)) => // _.
move: (@eqtype.eq_refl ssrnat.nat_eqType (SF_size s)) ; case: (@eqtype.eq_op ssrnat.nat_eqType (SF_size s) (SF_size s)) => // _.
have : ~ is_true (ssrnat.leq (S (S (SF_size s))) (S (SF_size s))).
have H0 := lt_n_Sn (SF_size s).
contradict H0.
apply SSR_leq in H0.
by apply le_not_lt, le_S_n.
case: (ssrnat.leq (S (S (SF_size s))) (S (SF_size s))) => // _.
move: (@eqtype.eq_refl ssrnat.nat_eqType (S (SF_size s))) ; case: (@eqtype.eq_op ssrnat.nat_eqType (S (SF_size s)) (S (SF_size s))) => // _.
rewrite H SF_lx_rev nth_rev SF_size_lx //=.
replace (ssrnat.subn (S (SF_size s'')) (S (SF_size s''))) with 0%nat by intuition.
simpl.
split ; apply Ropp_le_contravar ; apply (Hs' 0%nat) ; rewrite SF_size_cons ; by apply lt_O_Sn.
split.
rewrite Rmin_opp_Rmax -Hl.
simpl.
clear H.
revert ptd' ; move: (0) ; apply SF_cons_ind with (s := ptd) => [ h0 | h0 s IH] x0 s'.
by simpl.
set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
rewrite (SF_lx_cons (-fst h0,-snd h0) s'') rev_cons /=.
rewrite head_rcons.
by apply IH.
rewrite Rmax_opp_Rmin -Hh.
simpl.
clear H.
revert ptd' ; move: (0) ; apply SF_cons_dec with (s := ptd) => [ h0 | h0 s] x0 s'.
by simpl.
set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
rewrite (SF_lx_cons (-fst h0,-snd h0) s'') rev_cons /=.
rewrite head_rcons.
rewrite behead_rcons ; [ | rewrite size_rev SF_size_lx ; by apply lt_O_Sn].
rewrite unzip1_zip.
by rewrite last_rcons.
rewrite size_rcons size_behead ?size_rev SF_size_ly SF_size_lx //=.
revert ptd' ; apply SF_cons_ind with (s := ptd) => /= [x0 | h ptd' IH].
easy.
rewrite Riemann_sum_cons.
rewrite (SF_rev_cons (-fst h, -snd h) (mkSF_seq (- SF_h ptd') (seq.map (fun X : R * R => (- fst X, - snd X)) (SF_t ptd')))).
rewrite -IH => {IH}.
set s := {| SF_h := - SF_h ptd'; SF_t := seq.map (fun X : R * R => (- fst X, - snd X)) (SF_t ptd') |}.
rewrite Riemann_sum_rcons.
rewrite SF_lx_rev.
have H : (forall s x0, last x0 (rev s) = head x0 s).
move => T s0 x0.
case: s0 => [ | x1 s0] //=.
rewrite rev_cons.
by rewrite last_rcons.
rewrite H /=.
rewrite plus_comm.
apply: (f_equal (fun x => plus (scal x _) _)).
simpl ; ring.

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

Lemma is_RInt_SF (f : R -> V) (s : SF_seq) : SF_sorted Rle s -> let a := SF_h s in let b := last (SF_h s) (unzip1 (SF_t s)) in is_RInt (SF_fun (SF_map f s) zero) a b (Riemann_sum f s).
Proof.
apply SF_cons_ind with (s := s) => {s} [ x0 | x0 s IH] Hsort a b.
rewrite Riemann_sum_zero //.
by apply is_RInt_point.
-
rewrite Riemann_sum_cons.
apply is_RInt_Chasles with (SF_h s).
move: (proj1 Hsort) ; unfold a ; clear IH Hsort a b ; simpl => Hab.
eapply is_RInt_ext, is_RInt_const.
rewrite /Rmin /Rmax ; case: Rle_dec => // _ x Hx.
unfold SF_fun ; simpl.
case: Rlt_dec => //= H.
contradict H ; apply Rle_not_lt, Rlt_le, Hx.
move: Hab Hx ; apply SF_cons_dec with (s := s) => {s} /= [x1 | x1 s] Hab Hx.
case: Rle_dec (Rlt_le _ _ (proj2 Hx)) => //.
case: Rlt_dec (proj2 Hx) => //.
-
eapply is_RInt_ext, IH.
clear a IH.
revert b ; simpl.
rewrite /Rmin /Rmax ; case: Rle_dec => // Hab x Hx.
rewrite /SF_fun /=.
case: Rlt_dec => /= Hx0.
contradict Hx0.
apply Rle_not_lt.
eapply Rle_trans, Rlt_le, Hx.
by apply Hsort.
move: Hab Hx Hsort ; apply SF_cons_dec with (s := s) => {s} [x1 | x1 s] //= Hab Hx Hsort.
case: Hx => H H'.
contradict H' ; by apply Rle_not_lt, Rlt_le.
case: Rlt_dec => //= H.
contradict H ; by apply Rle_not_lt, Rlt_le, Hx.
contradict Hab.
apply (sorted_last ((SF_h s) :: (unzip1 (SF_t s))) O (proj2 Hsort) (lt_O_Sn _) (SF_h s)).
by apply Hsort.

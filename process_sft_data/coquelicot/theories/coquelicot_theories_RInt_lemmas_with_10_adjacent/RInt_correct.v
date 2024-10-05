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

Lemma norm_RInt_le_const : forall (f : R -> V) (a b : R) (lf : V) (M : R), a <= b -> (forall x, a <= x <= b -> norm (f x) <= M) -> is_RInt f a b lf -> norm lf <= (b - a) * M.
Proof.
intros f a b lf M Hab H Hf.
apply norm_RInt_le with (1 := Hab) (2 := H) (3 := Hf).
Admitted.

Lemma norm_RInt_le_const_abs : forall (f : R -> V) (a b : R) (lf : V) (M : R), (forall x, Rmin a b <= x <= Rmax a b -> norm (f x) <= M) -> is_RInt f a b lf -> norm lf <= Rabs (b - a) * M.
Proof.
intros f a b lf M H Hf.
unfold Rabs.
case Rcase_abs => Hab.
apply Rminus_lt in Hab.
rewrite Ropp_minus_distr.
apply is_RInt_swap in Hf.
rewrite <- norm_opp.
apply norm_RInt_le_const with (3 := Hf).
now apply Rlt_le.
intros x Hx.
apply H.
now rewrite -> Rmin_right, Rmax_left by now apply Rlt_le.
apply Rminus_ge in Hab.
apply Rge_le in Hab.
apply norm_RInt_le_const with (1 := Hab) (3 := Hf).
intros x Hx.
apply H.
Admitted.

Lemma is_RInt_fct_extend_fst (f : R -> U * V) (a b : R) (l : U * V) : is_RInt f a b l -> is_RInt (fun t => fst (f t)) a b (fst l).
Proof.
intros Hf P [eP HP].
destruct (Hf (fun u : U * V => P (fst u))) as [ef Hf'].
exists eP => y Hy.
apply HP.
apply Hy.
exists ef => y H1 H2.
replace (Riemann_sum (fun t : R => fst (f t)) y) with (fst (Riemann_sum f y)).
by apply Hf'.
clear.
apply SF_cons_ind with (s := y) => {y} [x0 | [x1 y0] y IH].
by rewrite /Riemann_sum /=.
Admitted.

Lemma is_RInt_fct_extend_snd (f : R -> U * V) (a b : R) (l : U * V) : is_RInt f a b l -> is_RInt (fun t => snd (f t)) a b (snd l).
Proof.
intros Hf P [eP HP].
destruct (Hf (fun u : U * V => P (snd u))) as [ef Hf'].
exists eP => y Hy.
apply HP.
apply Hy.
exists ef => y H1 H2.
replace (Riemann_sum (fun t : R => snd (f t)) y) with (snd (Riemann_sum f y)).
by apply Hf'.
clear.
apply SF_cons_ind with (s := y) => {y} [x0 | [x1 y0] y IH].
by rewrite /Riemann_sum /=.
Admitted.

Lemma is_RInt_fct_extend_pair (f : R -> U * V) (a b : R) lu lv : is_RInt (fun t => fst (f t)) a b lu -> is_RInt (fun t => snd (f t)) a b lv -> is_RInt f a b (lu,lv).
Proof.
move => H1 H2.
apply filterlim_locally => eps.
generalize (proj1 (filterlim_locally _ _) H1 eps) => {H1} ; intros [d1 H1].
generalize (proj1 (filterlim_locally _ _) H2 eps) => {H2} ; intros [d2 H2].
simpl in H1, H2.
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) => /= ptd Hstep Hptd.
rewrite (Riemann_sum_pair f ptd) ; simpl.
split.
apply H1 => //.
by apply Rlt_le_trans with (2 := Rmin_l d1 d2).
apply H2 => //.
Admitted.

Lemma ex_RInt_fct_extend_fst (f : R -> U * V) (a b : R) : ex_RInt f a b -> ex_RInt (fun t => fst (f t)) a b.
Proof.
intros [l Hl].
exists (fst l).
Admitted.

Lemma ex_RInt_fct_extend_snd (f : R -> U * V) (a b : R) : ex_RInt f a b -> ex_RInt (fun t => snd (f t)) a b.
Proof.
intros [l Hl].
exists (snd l).
Admitted.

Lemma ex_RInt_fct_extend_pair (f : R -> U * V) (a b : R) : ex_RInt (fun t => fst (f t)) a b -> ex_RInt (fun t => snd (f t)) a b -> ex_RInt f a b.
Proof.
move => [l1 H1] [l2 H2].
exists (l1,l2).
Admitted.

Lemma RInt_fct_extend_pair (U_RInt : (R -> U) -> R -> R -> U) (V_RInt : (R -> V) -> R -> R -> V) : (forall f a b l, is_RInt f a b l -> U_RInt f a b = l) -> (forall f a b l, is_RInt f a b l -> V_RInt f a b = l) -> forall f a b l, is_RInt f a b l -> (U_RInt (fun t => fst (f t)) a b, V_RInt (fun t => snd (f t)) a b) = l.
Proof.
intros HU HV f a b l Hf.
apply injective_projections ; simpl.
apply HU ; by apply is_RInt_fct_extend_fst.
Admitted.

Lemma is_RInt_unique (f : R -> V) (a b : R) (l : V) : is_RInt f a b l -> RInt f a b = l.
Proof.
Admitted.

Lemma opp_RInt_swap : forall f a b, ex_RInt f a b -> opp (RInt f a b) = RInt f b a.
Proof.
intros f a b [If HIf].
apply sym_eq, is_RInt_unique.
apply: is_RInt_swap.
apply RInt_correct.
Admitted.

Lemma RInt_ext (f g : R -> V) (a b : R) : (forall x, Rmin a b < x < Rmax a b -> f x = g x) -> RInt f a b = RInt g a b.
Proof.
intros Hfg.
apply eq_close.
apply: close_iota ; split ; apply is_RInt_ext.
exact Hfg.
intros t Ht.
Admitted.

Lemma RInt_point (a : R) (f : R -> V) : RInt f a a = zero.
Proof.
apply is_RInt_unique.
Admitted.

Lemma RInt_const (a b : R) (c : V) : RInt (fun _ => c) a b = scal (b - a) c.
Proof.
apply is_RInt_unique.
Admitted.

Lemma RInt_comp_lin (f : R -> V) (u v a b : R) : ex_RInt f (u * a + v) (u * b + v) -> RInt (fun y => scal u (f (u * y + v))) a b = RInt f (u * a + v) (u * b + v).
Proof.
intros Hf.
apply is_RInt_unique.
apply: is_RInt_comp_lin.
Admitted.

Lemma RInt_Chasles : forall f a b c, ex_RInt f a b -> ex_RInt f b c -> plus (RInt f a b) (RInt f b c) = RInt f a c.
Proof.
intros f a b c H1 H2.
apply sym_eq, is_RInt_unique.
Admitted.

Lemma RInt_scal (f : R -> V) (a b l : R) : ex_RInt f a b -> RInt (fun x => scal l (f x)) a b = scal l (RInt f a b).
Proof.
intros Hf.
apply is_RInt_unique.
apply: is_RInt_scal.
Admitted.

Lemma RInt_opp (f : R -> V) (a b : R) : ex_RInt f a b -> RInt (fun x => opp (f x)) a b = opp (RInt f a b).
Proof.
intros Hf.
apply is_RInt_unique.
apply: is_RInt_opp.
Admitted.

Lemma RInt_plus : forall f g a b, ex_RInt f a b -> ex_RInt g a b -> RInt (fun x => plus (f x) (g x)) a b = plus (RInt f a b) (RInt g a b).
Proof.
intros f g a b Hf Hg.
apply is_RInt_unique.
Admitted.

Lemma RInt_minus : forall f g a b, ex_RInt f a b -> ex_RInt g a b -> RInt (fun x => minus (f x) (g x)) a b = minus (RInt f a b) (RInt g a b).
Proof.
intros f g a b Hf Hg.
apply is_RInt_unique.
Admitted.

Lemma RInt_correct (f : R -> V) (a b : R) : ex_RInt f a b -> is_RInt f a b (RInt f a b).
Proof.
intros [If HIf].
erewrite is_RInt_unique ; exact HIf.

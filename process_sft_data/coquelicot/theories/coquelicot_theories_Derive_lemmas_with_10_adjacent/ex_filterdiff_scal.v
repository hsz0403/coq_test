Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Lim_seq Iter.
Require Import Hierarchy Continuity Equiv.
Open Scope R_scope.
Section LinearFct.
Context {K : AbsRing} {U V : NormedModule K}.
Record is_linear (l : U -> V) := { linear_plus : forall (x y : U), l (plus x y) = plus (l x) (l y) ; linear_scal : forall (k : K) (x : U), l (scal k x) = scal k (l x) ; linear_norm : exists M : R, 0 < M /\ (forall x : U, norm (l x) <= M * norm x) }.
End LinearFct.
Section Op_LinearFct.
Context {K : AbsRing} {V : NormedModule K}.
End Op_LinearFct.
Section Linear_domin.
Context {T : Type} {Kw K : AbsRing} {W : NormedModule Kw} {U V : NormedModule K}.
End Linear_domin.
Section Diff.
Context {K : AbsRing} {U : NormedModule K} {V : NormedModule K}.
Definition filterdiff (f : U -> V) F (l : U -> V) := is_linear l /\ forall x, is_filter_lim F x -> is_domin F (fun y : U => minus y x) (fun y => minus (minus (f y) (f x)) (l (minus y x))).
Definition ex_filterdiff (f : U -> V) F := exists (l : U -> V), filterdiff f F l.
End Diff.
Section Diff_comp.
Context {K : AbsRing} {U V W : NormedModule K}.
End Diff_comp.
Section Diff_comp2.
Context {K : AbsRing} {T U V : NormedModule K}.
Section Diff_comp2'.
Context {W : NormedModule K}.
End Diff_comp2'.
Context {W : NormedModule K}.
End Diff_comp2.
Section Operations.
Context {K : AbsRing} {V : NormedModule K}.
Local Ltac plus_grab e := repeat rewrite (plus_assoc _ e) -(plus_comm e) -(plus_assoc e).
End Operations.
Section Operations_fct.
Context {K : AbsRing} {U V : NormedModule K}.
End Operations_fct.
Section Derive.
Context {K : AbsRing} {V : NormedModule K}.
Definition is_derive (f : K -> V) (x : K) (l : V) := filterdiff f (locally x) (fun y : K => scal y l).
Definition ex_derive (f : K -> V) (x : K) := exists l : V, is_derive f x l.
End Derive.
Definition Derive (f : R -> R) (x : R) := real (Lim (fun h => (f (x+h) - f x)/h) 0).
Section Extensionality.
Context {K : AbsRing} {V : NormedModule K}.
End Extensionality.
Section Const.
Context {K : AbsRing} {V : NormedModule K}.
End Const.
Section Id.
Context {K : AbsRing}.
End Id.
Section Opp.
Context {K : AbsRing} {V : NormedModule K}.
End Opp.
Section Plus.
Context {K : AbsRing} {V : NormedModule K}.
End Plus.
Section Minus.
Context {K : AbsRing} {V : NormedModule K}.
End Minus.
Section Scal_l.
Context {K : AbsRing} {V : NormedModule K}.
End Scal_l.
Section Comp.
Context {K : AbsRing} {V : NormedModule K}.
End Comp.
Section ext_cont.
Context {U : UniformSpace}.
Definition extension_cont (f g : R -> U) (a x : R) : U := match Rle_dec x a with | left _ => f x | right _ => g x end.
End ext_cont.
Section ext_cont'.
Context {V : NormedModule R_AbsRing}.
End ext_cont'.
Section ext_C0.
Context {V : NormedModule R_AbsRing}.
Definition extension_C0 (f : R -> V) (a b : Rbar) (x : R) : V := match Rbar_le_dec a x with | left _ => match Rbar_le_dec x b with | left _ => f x | right _ => f (real b) end | right _ => f (real a) end.
End ext_C0.
Section ext_C1.
Context {V : NormedModule R_AbsRing}.
Definition extension_C1 (f df : R -> V) (a b : Rbar) (x : R) : V := match Rbar_le_dec a x with | left _ => match Rbar_le_dec x b with | left _ => f x | right _ => plus (f (real b)) (scal (x - real b) (df (real b))) end | right _ => plus (f (real a)) (scal (x - real a) (df (real a))) end.
End ext_C1.
Section NullDerivative.
Context {V : NormedModule R_AbsRing}.
End NullDerivative.
Fixpoint Derive_n (f : R -> R) (n : nat) x := match n with | O => f x | S n => Derive (Derive_n f n) x end.
Definition ex_derive_n f n x := match n with | O => True | S n => ex_derive (Derive_n f n) x end.
Definition is_derive_n f n x l := match n with | O => f x = l | S n => is_derive (Derive_n f n) x l end.

Lemma ex_filterdiff_comp'_2 : forall (f : T -> U) (g : T -> V) (h : U -> V -> W) x, ex_filterdiff f (locally x) -> ex_filterdiff g (locally x) -> ex_filterdiff (fun t => h (fst t) (snd t)) (locally (f x,g x)) -> ex_filterdiff (fun y : T => h (f y) (g y)) (locally x).
Proof.
intros f g h x [lf Df] [lg Dg] [lh Dh].
exists (fun x => lh (lf x,lg x)).
apply (filterdiff_comp'_2 f g h x lf lg (fun x y => lh (x,y))) ; try eassumption.
eapply filterdiff_ext_lin ; try eassumption.
Admitted.

Lemma filterdiff_id (F : (V -> Prop) -> Prop) : filterdiff (fun y => y) F (fun y => y).
Proof.
split.
by apply is_linear_id.
move => x Hx eps.
apply Hx ; exists eps => y /= Hy.
rewrite /minus plus_opp_r norm_zero.
apply Rmult_le_pos.
by apply Rlt_le, eps.
Admitted.

Lemma ex_filterdiff_id (F : (V -> Prop) -> Prop) : ex_filterdiff (fun y => y) F.
Proof.
eexists.
Admitted.

Lemma filterdiff_opp (F : (V -> Prop) -> Prop) : filterdiff opp F opp.
Proof.
split.
by apply is_linear_opp.
move => x Hx eps.
apply Hx.
exists eps => y /= Hy.
rewrite /minus -!opp_plus plus_opp_r norm_opp norm_zero.
apply Rmult_le_pos.
by apply Rlt_le, eps.
Admitted.

Lemma ex_filterdiff_opp (F : (V -> Prop) -> Prop) : ex_filterdiff opp F.
Proof.
eexists.
Admitted.

Lemma filterdiff_plus (F : (V * V -> Prop) -> Prop) : filterdiff (fun u => plus (fst u) (snd u)) F (fun u => plus (fst u) (snd u)).
Proof.
split.
by apply is_linear_plus.
move => x Hx eps.
apply Hx ; exists eps => u /= Hu.
set v := plus (plus _ _) _.
replace v with (minus (plus (fst u) (snd u)) (plus (fst x) (snd x))).
rewrite /minus plus_opp_r norm_zero.
apply Rmult_le_pos.
by apply Rlt_le, eps.
by apply sqrt_pos.
rewrite /v /minus -!plus_assoc ; apply f_equal.
Admitted.

Lemma ex_filterdiff_plus (F : (V * V -> Prop) -> Prop) : ex_filterdiff (fun u => plus (fst u) (snd u)) F.
Proof.
eexists.
Admitted.

Lemma filterdiff_minus (F : (V * V -> Prop) -> Prop) : filterdiff (fun u => minus (fst u) (snd u)) F (fun u => minus (fst u) (snd u)).
Proof.
split.
apply (is_linear_comp (fun u => (fst u, opp (snd u))) (fun u => plus (fst u) (snd u))).
apply is_linear_prod.
by apply is_linear_fst.
apply is_linear_comp.
by apply is_linear_snd.
by apply is_linear_opp.
by apply is_linear_plus.
move => x Hx eps.
apply Hx ; exists eps => u Hu.
simpl fst ; simpl snd.
set v := minus (plus _ (opp (fst x))) _.
replace v with (minus (minus (fst u) (snd u)) (minus (fst x) (snd x))).
rewrite /minus plus_opp_r norm_zero.
apply Rmult_le_pos.
by apply Rlt_le, eps.
by apply sqrt_pos.
rewrite /v /minus -!plus_assoc ; apply f_equal.
Admitted.

Lemma ex_filterdiff_minus (F : (V * V -> Prop) -> Prop) : ex_filterdiff (fun u => minus (fst u) (snd u)) F.
Proof.
eexists.
Admitted.

Lemma filterdiff_scal : forall {F : (K * V -> Prop) -> Prop} {FF : ProperFilter F} (x : K * V), is_filter_lim F x -> (forall (n m : K), mult n m = mult m n) -> filterdiff (fun t : K * V => scal (fst t) (snd t)) F (fun t => plus (scal (fst t) (snd x)) (scal (fst x) (snd t))).
Proof.
move => F FF [x1 x2] Hx Hcomm ; split.
-
apply (is_linear_comp (fun t : K * V => (scal (fst t) x2,scal x1 (snd t))) (fun t : V * V => plus (fst t) (snd t))).
apply is_linear_prod.
apply (is_linear_comp (fun t : K * V => fst t) (fun k : K => scal k x2)).
by apply is_linear_fst.
by apply is_linear_scal_l.
apply is_linear_comp.
by apply is_linear_snd.
by apply is_linear_scal_r.
apply is_linear_plus.
-
move => y Hy eps.
replace y with (x1,x2).
2: now apply is_filter_lim_unique with (1 := Hx).
clear y Hy.
apply Hx ; clear Hx.
apply: locally_le_locally_norm.
exists eps.
intros [y1 y2] H.
simpl.
set v := minus (minus _ _) _.
replace v with (scal (minus y1 x1) (minus y2 x2)).
apply Rle_trans with (1 := norm_scal _ _).
generalize (proj1 (sqrt_plus_sqr (abs (minus y1 x1)) (norm (minus y2 x2)))).
rewrite -> Rabs_pos_eq by apply abs_ge_0.
rewrite -> Rabs_pos_eq by apply norm_ge_0.
intros H'.
apply Rmult_le_compat.
apply abs_ge_0.
apply norm_ge_0.
apply Rlt_le, Rle_lt_trans with (2 := H).
apply Rle_trans with (2 := H').
apply Rmax_l.
apply Rle_trans with (2 := H').
apply Rmax_r.
rewrite /v /minus !scal_distr_l !scal_distr_r !opp_plus !scal_opp_r !scal_opp_l !opp_opp -!plus_assoc.
apply f_equal.
plus_grab (opp (scal x1 y2)).
apply f_equal.
plus_grab (opp (scal y1 x2)).
apply f_equal.
Admitted.

Lemma filterdiff_scal_l : forall {F} {FF : Filter F} (x : V), filterdiff (fun k : K => scal k x) F (fun k => scal k x).
Proof.
move => F FF x.
apply filterdiff_linear.
Admitted.

Lemma ex_filterdiff_scal_l : forall {F} {FF : Filter F} (x : V), ex_filterdiff (fun k : K => scal k x) F.
Proof.
eexists.
Admitted.

Lemma filterdiff_scal_r : forall {F} {FF : Filter F} (k : K), (forall (n m : K), mult n m = mult m n) -> filterdiff (fun x : V => scal k x) F (fun x => scal k x).
Proof.
move => F FF x Hcomm.
apply filterdiff_linear.
Admitted.

Lemma ex_filterdiff_scal_r : forall {F} {FF : Filter F} (k : K), (forall (n m : K), mult n m = mult m n) -> ex_filterdiff (fun x : V => scal k x) F.
Proof.
eexists.
Admitted.

Lemma filterdiff_mult {K : AbsRing} : forall {F} {FF : ProperFilter F} (x : K * K), is_filter_lim F x -> (forall (n m : K), mult n m = mult m n) -> filterdiff (fun t : K * K => mult (fst t) (snd t)) F (fun t => plus (mult (fst t) (snd x)) (mult (fst x) (snd t))).
Proof.
intros.
Admitted.

Lemma ex_filterdiff_mult {K : AbsRing} : forall {F} {FF : ProperFilter F} (x : K * K), is_filter_lim F x -> (forall (n m : K), mult n m = mult m n) -> ex_filterdiff (fun t : K * K => mult (fst t) (snd t)) F.
Proof.
eexists.
Admitted.

Lemma filterdiff_opp_fct {F} {FF : Filter F} (f lf : U -> V) : filterdiff f F lf -> filterdiff (fun t => opp (f t)) F (fun t => opp (lf t)).
Proof.
intro Df.
apply filterdiff_comp.
by [].
Admitted.

Lemma ex_filterdiff_opp_fct {F} {FF : Filter F} (f : U -> V) : ex_filterdiff f F -> ex_filterdiff (fun t => opp (f t)) F.
Proof.
intros [lf Df].
eexists.
Admitted.

Lemma filterdiff_plus_fct {F} {FF : Filter F} (f g : U -> V) (lf lg : U -> V) : filterdiff f F lf -> filterdiff g F lg -> filterdiff (fun u => plus (f u) (g u)) F (fun u => plus (lf u) (lg u)).
Proof.
intros Df Dg.
apply filterdiff_comp_2.
by [].
by [].
Admitted.

Lemma ex_filterdiff_plus_fct {F} {FF : Filter F} (f g : U -> V) : ex_filterdiff f F -> ex_filterdiff g F -> ex_filterdiff (fun u => plus (f u) (g u)) F.
Proof.
intros [lf Df] [lg Dg].
eexists.
Admitted.

Lemma ex_filterdiff_scal : forall {F} {FF : ProperFilter F} (x : K * V), is_filter_lim F x -> (forall (n m : K), mult n m = mult m n) -> ex_filterdiff (fun t : K * V => scal (fst t) (snd t)) F.
Proof.
eexists.
by apply (filterdiff_scal x).

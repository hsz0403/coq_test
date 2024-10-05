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

Lemma ex_filterdiff_minus_fct {F} {FF : Filter F} (f g : U -> V) : ex_filterdiff f F -> ex_filterdiff g F -> ex_filterdiff (fun u => minus (f u) (g u)) F.
Proof.
intros [lf Df] [lg Dg].
eexists.
Admitted.

Lemma filterdiff_scal_fct x (f : U -> K) (g : U -> V) lf lg : (forall (n m : K), mult n m = mult m n) -> filterdiff f (locally x) lf -> filterdiff g (locally x) lg -> filterdiff (fun t => scal (f t) (g t)) (locally x) (fun t => plus (scal (lf t) (g x)) (scal (f x) (lg t))).
Proof.
intros Hcomm Df Dg.
apply (filterdiff_comp'_2 f g scal x lf lg (fun k v => plus (scal k (g x)) (scal (f x) v))) => //.
Admitted.

Lemma ex_filterdiff_scal_fct x (f : U -> K) (g : U -> V) : (forall (n m : K), mult n m = mult m n) -> ex_filterdiff f (locally x) -> ex_filterdiff g (locally x) -> ex_filterdiff (fun t => scal (f t) (g t)) (locally x).
Proof.
intros Hcomm [lf Df] [lg Dg].
eexists.
Admitted.

Lemma filterdiff_scal_l_fct : forall {F} {FF : Filter F} (x : V) (f : U -> K) lf, filterdiff f F lf -> filterdiff (fun u => scal (f u) x) F (fun u => scal (lf u) x).
Proof.
move => F FF x f lf Df.
apply (filterdiff_comp f (fun k => scal k x) lf (fun k => scal k x)).
by [].
apply filterdiff_linear.
Admitted.

Lemma ex_filterdiff_scal_l_fct : forall {F} {FF : Filter F} (x : V) (f : U -> K), ex_filterdiff f F -> ex_filterdiff (fun u => scal (f u) x) F.
Proof.
intros F FF x f [lf Df].
eexists.
Admitted.

Lemma filterdiff_scal_r_fct : forall {F} {FF : Filter F} (k : K) (f lf : U -> V), (forall (n m : K), mult n m = mult m n) -> filterdiff f F lf -> filterdiff (fun x => scal k (f x)) F (fun x => scal k (lf x)).
Proof.
move => F FF k f lf Hcomm Df.
apply (filterdiff_comp f (fun x => scal k x) lf (fun x => scal k x)).
by [].
apply filterdiff_linear.
Admitted.

Lemma ex_filterdiff_scal_r_fct : forall {F} {FF : Filter F} (k : K) (f : U -> V), (forall (n m : K), mult n m = mult m n) -> ex_filterdiff f F -> ex_filterdiff (fun x => scal k (f x)) F.
Proof.
move => F FF k f Hcomm [lf Df].
eexists.
Admitted.

Lemma filterdiff_mult_fct {K : AbsRing} {U : NormedModule K} (f g : U -> K) x (lf lg : U -> K) : (forall (n m : K), mult n m = mult m n) -> filterdiff f (locally x) lf -> filterdiff g (locally x) lg -> filterdiff (fun t => mult (f t) (g t)) (locally x) (fun t => plus (mult (lf t) (g x)) (mult (f x) (lg t))).
Proof.
intros.
Admitted.

Lemma ex_filterdiff_mult_fct {K : AbsRing} {U : NormedModule K} (f g : U -> K) x : (forall (n m : K), mult n m = mult m n) -> ex_filterdiff f (locally x) -> ex_filterdiff g (locally x) -> ex_filterdiff (fun t => mult (f t) (g t)) (locally x).
Proof.
intros Hcomm [lf Df] [lg Dg].
eexists.
Admitted.

Lemma ex_derive_filterdiff : forall (f : K -> V) (x : K), ex_derive f x <-> ex_filterdiff f (locally x).
Proof.
intros f x.
split ; case => d Df.
-
eexists.
exact Df.
-
exists (d one).
split.
apply is_linear_scal_l.
simpl => t Ht.
destruct Df as [Ld Df].
simpl in Df.
apply domin_rw_r with (2 := Df t Ht).
apply equiv_ext_loc.
apply filter_imp with (2 := filter_true) => y /= _.
apply f_equal.
rewrite -linear_scal //=.
Admitted.

Lemma is_derive_Reals (f : R -> R) (x l : R) : is_derive f x l <-> derivable_pt_lim f x l.
Proof.
apply iff_sym.
split => Hf.
+
split.
apply @is_linear_scal_l.
simpl => y Hy eps.
rewrite -(is_filter_lim_locally_unique _ _ Hy) ; clear y Hy.
case: (Hf eps (cond_pos _)) => {Hf} d Hf.
exists d => y /= Hy.
case: (Req_dec y x) => Hxy.
rewrite Hxy /norm /scal /= /abs /minus /plus /opp /mult /=.
ring_simplify (f x + - f x + - ((x + - x) * l)).
ring_simplify (x + - x).
rewrite Rabs_R0 Rmult_0_r.
by apply Rle_refl.
apply Rle_div_l.
apply Rabs_pos_lt.
by apply Rminus_eq_contra.
rewrite -Rabs_div.
2: by apply Rminus_eq_contra.
rewrite /scal /= /minus /plus /opp /mult /=.
replace ((f y + - f x + - ((y + - x) * l)) / (y + - x)) with ((f (x + (y-x)) - f x) / (y-x) - l).
2: ring_simplify (x + (y - x)) ; field ; by apply Rminus_eq_contra.
apply Rlt_le, Hf.
by apply Rminus_eq_contra.
by [].
+
move => e He.
destruct Hf as [_ Hf].
specialize (Hf x (fun P H => H)).
destruct (Hf (pos_div_2 (mkposreal _ He))) as [delta Hd].
exists delta => h Hh0 Hh.
apply Rle_lt_trans with (e / 2).
simpl in Hd.
replace ((f (x + h) - f x) / h - l) with ((f (x + h) + - f x + - ((x + h + - x) * l)) / (x + h + - x)).
2: by field.
rewrite Rabs_div.
2: by ring_simplify (x + h + - x).
apply Rle_div_l.
now ring_simplify (x + h + - x) ; apply Rabs_pos_lt.
apply Hd.
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /=.
by ring_simplify (x + h + - x).
apply Rlt_div_l, Rminus_lt_0 ; ring_simplify.
by apply Rlt_0_2.
Admitted.

Lemma is_derive_unique f x l : is_derive f x l -> Derive f x = l.
Proof.
intros H.
apply (@f_equal _ _ real _ l).
apply is_lim_unique.
apply is_lim_spec.
apply is_derive_Reals in H.
intros eps.
destruct (H eps (cond_pos _)) as [d Hd].
exists d => h.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= Ropp_0 Rplus_0_r.
intros Hu Zu.
Admitted.

Lemma Derive_correct f x : ex_derive f x -> is_derive f x (Derive f x).
Proof.
intros (l,H).
cut (Derive f x = l).
intros ; rewrite H0 ; apply H.
Admitted.

Lemma ex_derive_Reals_0 (f : R -> R) (x : R) : ex_derive f x -> derivable_pt f x.
Proof.
move => Hf.
apply Derive_correct in Hf.
apply is_derive_Reals in Hf.
Admitted.

Lemma ex_derive_Reals_1 (f : R -> R) (x : R) : derivable_pt f x -> ex_derive f x.
Proof.
case => l Hf.
exists l.
Admitted.

Lemma Derive_Reals (f : R -> R) (x : R) (pr : derivable_pt f x) : derive_pt f x pr = Derive f x.
Proof.
apply sym_eq, is_derive_unique.
case: pr => /= l Hf.
Admitted.

Lemma is_derive_ext_loc : forall (f g : K -> V) (x : K) (l : V), locally x (fun t : K => f t = g t) -> is_derive f x l -> is_derive g x l.
Proof.
intros f g x l Heq Hf.
Admitted.

Lemma ex_derive_ext_loc : forall (f g : K -> V) (x : K), locally x (fun t : K => f t = g t) -> ex_derive f x -> ex_derive g x.
Proof.
intros f g x Hfg (l,Hf).
exists l.
Admitted.

Lemma is_derive_ext : forall (f g : K -> V) (x : K) (l : V), (forall t : K, f t = g t) -> is_derive f x l -> is_derive g x l.
Proof.
intros f g x l Heq Hf.
apply: filterdiff_ext_locally Hf.
Admitted.

Lemma ex_derive_ext : forall (f g : K -> V) (x : K), (forall t : K, f t = g t) -> ex_derive f x -> ex_derive g x.
Proof.
intros f g x Heq [l Hf].
Admitted.

Lemma ex_derive_continuous (f : K -> V) (x : K) : ex_derive f x -> continuous f x.
Proof.
intros.
apply @filterdiff_continuous.
by apply ex_derive_filterdiff.

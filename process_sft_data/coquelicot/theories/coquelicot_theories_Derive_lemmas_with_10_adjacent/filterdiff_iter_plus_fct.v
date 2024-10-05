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

Lemma filterdiff_minus_fct {F} {FF : Filter F} (f g : U -> V) (lf lg : U -> V) : filterdiff f F lf -> filterdiff g F lg -> filterdiff (fun u => minus (f u) (g u)) F (fun u => minus (lf u) (lg u)).
Proof.
intros Df Dg.
apply filterdiff_comp_2.
by [].
by [].
Admitted.

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

Lemma filterdiff_iter_plus_fct {I} {F} {FF : Filter F} (l : list I) (f : I -> U -> V) df (x : U) : (forall (j : I), List.In j l -> filterdiff (f j) F (df j)) -> filterdiff (fun y => iter plus zero l (fun j => f j y)) F (fun x => iter plus zero l (fun j => df j x)).
Proof.
intros Hf.
induction l ; simpl in * |- *.
apply filterdiff_const.
apply filterdiff_plus_fct.
apply Hf.
by left.
apply IHl ; intros.
apply Hf.
by right.

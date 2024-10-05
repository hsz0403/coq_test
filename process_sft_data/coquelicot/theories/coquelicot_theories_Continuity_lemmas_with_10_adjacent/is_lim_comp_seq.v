Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Compactness Lim_seq.
Definition is_lim (f : R -> R) (x l : Rbar) := filterlim f (Rbar_locally' x) (Rbar_locally l).
Definition is_lim' (f : R -> R) (x l : Rbar) := match l with | Finite l => forall eps : posreal, Rbar_locally' x (fun y => Rabs (f y - l) < eps) | p_infty => forall M : R, Rbar_locally' x (fun y => M < f y) | m_infty => forall M : R, Rbar_locally' x (fun y => f y < M) end.
Definition ex_lim (f : R -> R) (x : Rbar) := exists l : Rbar, is_lim f x l.
Definition ex_finite_lim (f : R -> R) (x : Rbar) := exists l : R, is_lim f x l.
Definition Lim (f : R -> R) (x : Rbar) := Lim_seq (fun n => f (Rbar_loc_seq x n)).
Definition continuity_2d_pt f x y := forall eps : posreal, locally_2d (fun u v => Rabs (f u v - f x y) < eps) x y.
Section Continuity.
Context {T U : UniformSpace}.
Definition continuous_on (D : T -> Prop) (f : T -> U) := forall x, D x -> filterlim f (within D (locally x)) (locally (f x)).
Definition continuous (f : T -> U) (x : T) := filterlim f (locally x) (locally (f x)).
End Continuity.
Section Continuity_op.
Context {U : UniformSpace} {K : AbsRing} {V : NormedModule K}.
End Continuity_op.
Section UnifCont.
Context {V : UniformSpace}.
End UnifCont.
Section UnifCont_N.
Context {K : AbsRing} {V : NormedModule K}.
End UnifCont_N.

Lemma is_lim_spec : forall f x l, is_lim' f x l <-> is_lim f x l.
Proof.
destruct l as [l| |] ; split.
-
intros H P [eps LP].
unfold filtermap.
generalize (H eps).
apply filter_imp.
intros u.
apply LP.
-
intros H eps.
apply (H (fun y => Rabs (y - l) < eps)).
now exists eps.
-
intros H P [M LP].
unfold filtermap.
generalize (H M).
apply filter_imp.
intros u.
apply LP.
-
intros H M.
apply (H (fun y => M < y)).
now exists M.
-
intros H P [M LP].
unfold filtermap.
generalize (H M).
apply filter_imp.
intros u.
apply LP.
-
intros H M.
apply (H (fun y => y < M)).
Admitted.

Lemma is_lim_Reals_0 (f : R -> R) (x l : R) : is_lim f x l -> limit1_in f (fun y => y <> x) l x.
Proof.
intros H e He.
apply is_lim_spec in H.
destruct (H (mkposreal e He)) as [d Hd].
exists d ; split.
apply cond_pos.
intros y [H1 H2].
Admitted.

Lemma is_lim_Reals_1 (f : R -> R) (x l : R) : limit1_in f (fun y => y <> x) l x -> is_lim f x l.
Proof.
intros H.
apply is_lim_spec.
intros [e He].
destruct (H e He) as [d [Hd H']].
exists (mkposreal d Hd).
intros y Hy Hxy.
apply (H' y).
Admitted.

Lemma is_lim_Reals (f : R -> R) (x l : R) : is_lim f x l <-> limit1_in f (fun y => y <> x) l x.
Proof.
Admitted.

Lemma is_lim_comp' : forall {T} {F} {FF : @Filter T F} (f : T -> R) (g : R -> R) (x l : Rbar), filterlim f F (Rbar_locally x) -> is_lim g x l -> F (fun y => Finite (f y) <> x) -> filterlim (fun y => g (f y)) F (Rbar_locally l).
Proof.
intros T F FF f g x l Lf Lg Hf.
revert Lg.
apply filterlim_comp.
intros P HP.
destruct x as [x| |] ; try now apply Lf.
specialize (Lf _ HP).
unfold filtermap in Lf |- *.
generalize (filter_and _ _ Hf Lf).
apply filter_imp.
intros y [H Hi].
apply Hi.
contradict H.
Admitted.

Lemma is_lim_unique (f : R -> R) (x l : Rbar) : is_lim f x l -> Lim f x = l.
Proof.
intros.
unfold Lim.
rewrite (is_lim_seq_unique _ l) //.
apply (is_lim_comp_seq f _ x l H).
exists 1%nat => n Hn.
case: x {H} => [x | | ] //=.
apply Rbar_finite_neq, Rgt_not_eq, Rminus_lt_0.
ring_simplify.
by apply RinvN_pos.
Admitted.

Lemma Lim_correct (f : R -> R) (x : Rbar) : ex_lim f x -> is_lim f x (Lim f x).
Proof.
intros (l,H).
replace (Lim f x) with l.
apply H.
Admitted.

Lemma ex_finite_lim_correct (f : R -> R) (x : Rbar) : ex_finite_lim f x <-> ex_lim f x /\ is_finite (Lim f x).
Proof.
split.
case => l Hf.
move: (is_lim_unique f x l Hf) => Hf0.
split.
by exists l.
by rewrite Hf0.
case ; case => l Hf Hf0.
exists (real l).
rewrite -(is_lim_unique _ _ _ Hf).
rewrite Hf0.
Admitted.

Lemma Lim_correct' (f : R -> R) (x : Rbar) : ex_finite_lim f x -> is_lim f x (real (Lim f x)).
Proof.
intro Hf.
apply ex_finite_lim_correct in Hf.
rewrite (proj2 Hf).
Admitted.

Lemma is_lim_ext_loc (f g : R -> R) (x l : Rbar) : Rbar_locally' x (fun y => f y = g y) -> is_lim f x l -> is_lim g x l.
Proof.
Admitted.

Lemma ex_lim_ext_loc (f g : R -> R) (x : Rbar) : Rbar_locally' x (fun y => f y = g y) -> ex_lim f x -> ex_lim g x.
Proof.
move => H [l Hf].
exists l.
Admitted.

Lemma Lim_ext_loc (f g : R -> R) (x : Rbar) : Rbar_locally' x (fun y => f y = g y) -> Lim g x = Lim f x.
Proof.
move => H.
apply sym_eq.
apply Lim_seq_ext_loc.
Admitted.

Lemma is_lim_ext (f g : R -> R) (x l : Rbar) : (forall y, f y = g y) -> is_lim f x l -> is_lim g x l.
Proof.
move => H.
apply is_lim_ext_loc.
Admitted.

Lemma ex_lim_ext (f g : R -> R) (x : Rbar) : (forall y, f y = g y) -> ex_lim f x -> ex_lim g x.
Proof.
move => H [l Hf].
exists l.
Admitted.

Lemma Lim_ext (f g : R -> R) (x : Rbar) : (forall y, f y = g y) -> Lim g x = Lim f x.
Proof.
move => H.
apply Lim_ext_loc.
Admitted.

Lemma is_lim_comp_seq (f : R -> R) (u : nat -> R) (x l : Rbar) : is_lim f x l -> eventually (fun n => Finite (u n) <> x) -> is_lim_seq u x -> is_lim_seq (fun n => f (u n)) l.
Proof.
intros Lf Hu Lu.
exact (is_lim_comp' u f x l Lu Lf Hu).

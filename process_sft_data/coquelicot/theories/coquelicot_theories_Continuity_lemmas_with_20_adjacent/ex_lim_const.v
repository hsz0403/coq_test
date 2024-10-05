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

Lemma is_lim_comp_seq (f : R -> R) (u : nat -> R) (x l : Rbar) : is_lim f x l -> eventually (fun n => Finite (u n) <> x) -> is_lim_seq u x -> is_lim_seq (fun n => f (u n)) l.
Proof.
intros Lf Hu Lu.
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

Lemma is_lim_comp (f g : R -> R) (x k l : Rbar) : is_lim f l k -> is_lim g x l -> Rbar_locally' x (fun y => Finite (g y) <> l) -> is_lim (fun x => f (g x)) x k.
Proof.
intros Lf Lg Hg.
Admitted.

Lemma ex_lim_comp (f g : R -> R) (x : Rbar) : ex_lim f (Lim g x) -> ex_lim g x -> Rbar_locally' x (fun y => Finite (g y) <> Lim g x) -> ex_lim (fun x => f (g x)) x.
Proof.
intros.
exists (Lim f (Lim g x)).
apply is_lim_comp with (Lim g x).
by apply Lim_correct.
by apply Lim_correct.
Admitted.

Lemma Lim_comp (f g : R -> R) (x : Rbar) : ex_lim f (Lim g x) -> ex_lim g x -> Rbar_locally' x (fun y => Finite (g y) <> Lim g x) -> Lim (fun x => f (g x)) x = Lim f (Lim g x).
Proof.
intros.
apply is_lim_unique.
apply is_lim_comp with (Lim g x).
by apply Lim_correct.
by apply Lim_correct.
Admitted.

Lemma is_lim_id (x : Rbar) : is_lim (fun y => y) x x.
Proof.
intros P HP.
apply filterlim_id.
Admitted.

Lemma ex_lim_id (x : Rbar) : ex_lim (fun y => y) x.
Proof.
exists x.
Admitted.

Lemma Lim_id (x : Rbar) : Lim (fun y => y) x = x.
Proof.
apply is_lim_unique.
Admitted.

Lemma is_lim_const (a : R) (x : Rbar) : is_lim (fun _ => a) x a.
Proof.
intros P HP.
Admitted.

Lemma Lim_const (a : R) (x : Rbar) : Lim (fun _ => a) x = a.
Proof.
apply is_lim_unique.
Admitted.

Lemma is_lim_opp (f : R -> R) (x l : Rbar) : is_lim f x l -> is_lim (fun y => - f y) x (Rbar_opp l).
Proof.
intros Cf.
eapply filterlim_comp.
apply Cf.
Admitted.

Lemma ex_lim_opp (f : R -> R) (x : Rbar) : ex_lim f x -> ex_lim (fun y => - f y) x.
Proof.
case => l Hf.
exists (Rbar_opp l).
Admitted.

Lemma Lim_opp (f : R -> R) (x : Rbar) : Lim (fun y => - f y) x = Rbar_opp (Lim f x).
Proof.
rewrite -Lim_seq_opp.
Admitted.

Lemma is_lim_plus (f g : R -> R) (x lf lg l : Rbar) : is_lim f x lf -> is_lim g x lg -> is_Rbar_plus lf lg l -> is_lim (fun y => f y + g y) x l.
Proof.
intros Cf Cg Hp.
eapply filterlim_comp_2 ; try eassumption.
Admitted.

Lemma is_lim_plus' (f g : R -> R) (x : Rbar) (lf lg : R) : is_lim f x lf -> is_lim g x lg -> is_lim (fun y => f y + g y) x (lf + lg).
Proof.
intros Hf Hg.
eapply is_lim_plus.
by apply Hf.
by apply Hg.
Admitted.

Lemma ex_lim_plus (f g : R -> R) (x : Rbar) : ex_lim f x -> ex_lim g x -> ex_Rbar_plus (Lim f x) (Lim g x) -> ex_lim (fun y => f y + g y) x.
Proof.
move => /Lim_correct Hf /Lim_correct Hg Hl.
exists (Rbar_plus (Lim f x) (Lim g x)).
eapply is_lim_plus ; try eassumption.
Admitted.

Lemma Lim_plus (f g : R -> R) (x : Rbar) : ex_lim f x -> ex_lim g x -> ex_Rbar_plus (Lim f x) (Lim g x) -> Lim (fun y => f y + g y) x = Rbar_plus (Lim f x) (Lim g x).
Proof.
move => /Lim_correct Hf /Lim_correct Hg Hl.
apply is_lim_unique.
eapply is_lim_plus ; try eassumption.
Admitted.

Lemma is_lim_minus (f g : R -> R) (x lf lg l : Rbar) : is_lim f x lf -> is_lim g x lg -> is_Rbar_minus lf lg l -> is_lim (fun y => f y - g y) x l.
Proof.
move => Hf Hg Hl.
eapply is_lim_plus ; try eassumption.
Admitted.

Lemma is_lim_minus' (f g : R -> R) (x : Rbar) (lf lg : R) : is_lim f x lf -> is_lim g x lg -> is_lim (fun y => f y - g y) x (lf - lg).
Proof.
intros Hf Hg.
eapply is_lim_minus ; try eassumption.
Admitted.

Lemma ex_lim_minus (f g : R -> R) (x : Rbar) : ex_lim f x -> ex_lim g x -> ex_Rbar_minus (Lim f x) (Lim g x) -> ex_lim (fun y => f y - g y) x.
Proof.
move => Hf Hg Hl.
apply ex_lim_plus.
by apply Hf.
apply ex_lim_opp.
by apply Hg.
rewrite Lim_opp.
Admitted.

Lemma Lim_minus (f g : R -> R) (x : Rbar) : ex_lim f x -> ex_lim g x -> ex_Rbar_minus (Lim f x) (Lim g x) -> Lim (fun y => f y - g y) x = Rbar_minus (Lim f x) (Lim g x).
Proof.
move => Hf Hg Hl.
rewrite Lim_plus.
by rewrite Lim_opp.
by apply Hf.
apply ex_lim_opp.
by apply Hg.
rewrite Lim_opp.
Admitted.

Lemma is_lim_inv (f : R -> R) (x l : Rbar) : is_lim f x l -> l <> 0 -> is_lim (fun y => / f y) x (Rbar_inv l).
Proof.
intros Hf Hl.
apply filterlim_comp with (1 := Hf).
Admitted.

Lemma ex_lim_inv (f : R -> R) (x : Rbar) : ex_lim f x -> Lim f x <> 0 -> ex_lim (fun y => / f y) x.
Proof.
move => /Lim_correct Hf Hlf.
exists (Rbar_inv (Lim f x)).
Admitted.

Lemma Lim_inv (f : R -> R) (x : Rbar) : ex_lim f x -> Lim f x <> 0 -> Lim (fun y => / f y) x = Rbar_inv (Lim f x).
Proof.
move => /Lim_correct Hf Hlf.
apply is_lim_unique.
Admitted.

Lemma is_lim_mult (f g : R -> R) (x lf lg : Rbar) : is_lim f x lf -> is_lim g x lg -> ex_Rbar_mult lf lg -> is_lim (fun y => f y * g y) x (Rbar_mult lf lg).
Proof.
intros Cf Cg Hp.
eapply filterlim_comp_2 ; try eassumption.
Admitted.

Lemma ex_lim_mult (f g : R -> R) (x : Rbar) : ex_lim f x -> ex_lim g x -> ex_Rbar_mult (Lim f x) (Lim g x) -> ex_lim (fun y => f y * g y) x.
Proof.
move => /Lim_correct Hf /Lim_correct Hg Hl.
exists (Rbar_mult (Lim f x) (Lim g x)).
Admitted.

Lemma Lim_mult (f g : R -> R) (x : Rbar) : ex_lim f x -> ex_lim g x -> ex_Rbar_mult (Lim f x) (Lim g x) -> Lim (fun y => f y * g y) x = Rbar_mult (Lim f x) (Lim g x).
Proof.
move => /Lim_correct Hf /Lim_correct Hg Hl.
apply is_lim_unique.
Admitted.

Lemma is_lim_scal_l (f : R -> R) (a : R) (x l : Rbar) : is_lim f x l -> is_lim (fun y => a * f y) x (Rbar_mult a l).
Proof.
move => Hf.
case: (Req_dec 0 a) => [<- {a} | Ha].
rewrite Rbar_mult_0_l.
apply is_lim_ext with (fun _ => 0).
move => y ; by rewrite Rmult_0_l.
by apply is_lim_const.
apply is_lim_mult.
by apply is_lim_const.
by apply Hf.
apply sym_not_eq in Ha.
Admitted.

Lemma ex_lim_scal_l (f : R -> R) (a : R) (x : Rbar) : ex_lim f x -> ex_lim (fun y => a * f y) x.
Proof.
case => l Hf.
exists (Rbar_mult a l).
Admitted.

Lemma ex_lim_const (a : R) (x : Rbar) : ex_lim (fun _ => a) x.
Proof.
exists a.
by apply is_lim_const.

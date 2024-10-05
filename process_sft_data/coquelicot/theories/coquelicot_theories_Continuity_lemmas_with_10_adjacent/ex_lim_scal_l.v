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

Lemma Lim_scal_l (f : R -> R) (a : R) (x : Rbar) : Lim (fun y => a * f y) x = Rbar_mult a (Lim f x).
Proof.
Admitted.

Lemma is_lim_scal_r (f : R -> R) (a : R) (x l : Rbar) : is_lim f x l -> is_lim (fun y => f y * a) x (Rbar_mult l a).
Proof.
move => Hf.
rewrite Rbar_mult_comm.
apply is_lim_ext with (fun y => a * f y).
move => y ; by apply Rmult_comm.
Admitted.

Lemma ex_lim_scal_r (f : R -> R) (a : R) (x : Rbar) : ex_lim f x -> ex_lim (fun y => f y * a) x.
Proof.
case => l Hf.
exists (Rbar_mult l a).
Admitted.

Lemma Lim_scal_r (f : R -> R) (a : R) (x : Rbar) : Lim (fun y => f y * a) x = Rbar_mult (Lim f x) a.
Proof.
rewrite Rbar_mult_comm -Lim_seq_scal_l.
apply Lim_seq_ext.
Admitted.

Lemma is_lim_div (f g : R -> R) (x lf lg : Rbar) : is_lim f x lf -> is_lim g x lg -> lg <> 0 -> ex_Rbar_div lf lg -> is_lim (fun y => f y / g y) x (Rbar_div lf lg).
Proof.
move => Hf Hg Hlg Hl.
apply is_lim_mult ; try assumption.
Admitted.

Lemma ex_lim_div (f g : R -> R) (x : Rbar) : ex_lim f x -> ex_lim g x -> Lim g x <> 0 -> ex_Rbar_div (Lim f x) (Lim g x) -> ex_lim (fun y => f y / g y) x.
Proof.
move => Hf Hg Hlg Hl.
apply ex_lim_mult ; try assumption.
now apply ex_lim_inv.
Admitted.

Lemma Lim_div (f g : R -> R) (x : Rbar) : ex_lim f x -> ex_lim g x -> Lim g x <> 0 -> ex_Rbar_div (Lim f x) (Lim g x) -> Lim (fun y => f y / g y) x = Rbar_div (Lim f x) (Lim g x).
Proof.
move => Hf Hg Hlg Hl.
apply is_lim_unique.
Admitted.

Lemma is_lim_comp_lin (f : R -> R) (a b : R) (x l : Rbar) : is_lim f (Rbar_plus (Rbar_mult a x) b) l -> a <> 0 -> is_lim (fun y => f (a * y + b)) x l.
Proof.
move => Hf Ha.
apply is_lim_comp with (Rbar_plus (Rbar_mult a x) b).
by apply Hf.
eapply is_lim_plus.
apply is_lim_scal_l.
apply is_lim_id.
apply is_lim_const.
apply Rbar_plus_correct.
case: (Rbar_mult a x) => //.
case: x {Hf} => [x | | ] //=.
exists (mkposreal _ Rlt_0_1) => y _ Hy.
apply Rbar_finite_neq, Rminus_not_eq ; ring_simplify (a * y + b - (a * x + b)).
rewrite -Rmult_minus_distr_l.
apply Rmult_integral_contrapositive ; split.
by [].
by apply Rminus_eq_contra.
exists 0 => x Hx.
apply sym_not_eq in Ha.
case: Rle_dec => // H.
case: Rle_lt_or_eq_dec => //.
exists 0 => x Hx.
apply sym_not_eq in Ha.
case: Rle_dec => // H.
Admitted.

Lemma ex_lim_comp_lin (f : R -> R) (a b : R) (x : Rbar) : ex_lim f (Rbar_plus (Rbar_mult a x) b) -> ex_lim (fun y => f (a * y + b)) x.
Proof.
case => l Hf.
case: (Req_dec a 0) => [-> {a Hf} | Ha].
apply ex_lim_ext with (fun _ => f b).
move => y ; by rewrite Rmult_0_l Rplus_0_l.
by apply ex_lim_const.
Admitted.

Lemma Lim_comp_lin (f : R -> R) (a b : R) (x : Rbar) : ex_lim f (Rbar_plus (Rbar_mult a x) b) -> a <> 0 -> Lim (fun y => f (a * y + b)) x = Lim f (Rbar_plus (Rbar_mult a x) b).
Proof.
move => Hf Ha.
apply is_lim_unique.
apply is_lim_comp_lin.
by apply Lim_correct.
Admitted.

Lemma ex_lim_scal_l (f : R -> R) (a : R) (x : Rbar) : ex_lim f x -> ex_lim (fun y => a * f y) x.
Proof.
case => l Hf.
exists (Rbar_mult a l).
by apply is_lim_scal_l.

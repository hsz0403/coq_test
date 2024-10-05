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

Lemma is_lim_const (a : R) (x : Rbar) : is_lim (fun _ => a) x a.
Proof.
intros P HP.
Admitted.

Lemma ex_lim_const (a : R) (x : Rbar) : ex_lim (fun _ => a) x.
Proof.
exists a.
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

Lemma Lim_id (x : Rbar) : Lim (fun y => y) x = x.
Proof.
apply is_lim_unique.
by apply is_lim_id.

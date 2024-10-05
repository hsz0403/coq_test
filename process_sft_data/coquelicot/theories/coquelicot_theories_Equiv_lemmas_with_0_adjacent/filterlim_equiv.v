Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Hierarchy.
Definition is_domin {T} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} (F : (T -> Prop) -> Prop) (f : T -> U) (g : T -> V) := forall eps : posreal, F (fun x => norm (g x) <= eps * norm (f x)).
Definition is_equiv {T} {K : AbsRing} {V : NormedModule K} (F : (T -> Prop) -> Prop) (f g : T -> V) := is_domin F g (fun x => minus (g x) (f x)).
Section Equiv.
Context {T : Type} {K : AbsRing} {V : NormedModule K}.
End Equiv.
Section Domin.
Context {T : Type} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv}.
End Domin.
Section Equiv_VS.
Context {T : Type} {K : AbsRing} {V : NormedModule K}.
End Equiv_VS.
Section Domin_comp.
Context {T1 T2 : Type} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} (F : (T1 -> Prop) -> Prop) {FF : Filter F} (G : (T2 -> Prop) -> Prop) {FG : Filter G}.
End Domin_comp.

Lemma filterlim_equiv : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R) (l : Rbar), is_equiv F f g -> filterlim f F (Rbar_locally l) -> filterlim g F (Rbar_locally l).
Proof.
intros T F FF f g [l| |] Hfg Hf P [eps HP] ; apply equiv_sym in Hfg ; unfold filtermap.
-
assert (He: 0 < eps / 2 / (Rabs l + 1)).
apply Rdiv_lt_0_compat.
apply is_pos_div_2.
apply Rplus_le_lt_0_compat.
apply Rabs_pos.
apply Rlt_0_1.
pose ineqs (y : R) := Rabs (y - l) < eps/2 /\ Rabs y <= Rabs l + 1.
assert (Hl: Rbar_locally l ineqs).
assert (H: 0 < Rmin (eps / 2) 1).
apply Rmin_case.
apply is_pos_div_2.
apply Rlt_0_1.
exists (mkposreal _ H).
simpl.
intros x Hx.
split.
apply Rlt_le_trans with (1 := Hx).
apply Rmin_l.
apply Rabs_le_between'.
apply Rle_trans with (1 := Rabs_triang_inv2 _ _).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx).
apply Rmin_r.
generalize (filter_and _ (fun (x : T) => ineqs (f x)) (Hfg (mkposreal _ He)) (Hf _ Hl)).
apply filter_imp.
simpl.
intros x [H1 [H2 H3]].
apply HP.
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /=.
replace (g x + - l) with ((f x - l) + -(f x - g x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (eps / 2 + eps / 2 / (Rabs l + 1) * (Rabs l + 1)).
apply Rplus_lt_le_compat with (1 := H2).
rewrite Rabs_Ropp.
apply Rle_trans with (1 := H1).
apply Rmult_le_compat_l with (2 := H3).
now apply Rlt_le.
field.
apply Rgt_not_eq.
apply Rplus_le_lt_0_compat.
apply Rabs_pos.
apply Rlt_0_1.
-
pose ineq (y : R) := Rmax 0 (2 * eps) < y.
assert (Hl: Rbar_locally' p_infty ineq).
now exists (Rmax 0 (2 * eps)).
generalize (filter_and _ (fun (x : T) => ineq (f x)) (Hfg (mkposreal _ pos_half_prf)) (Hf _ Hl)).
apply filter_imp.
simpl.
intros x [H1 H2].
apply HP.
apply Rabs_le_between' in H1.
generalize (Rplus_le_compat_l (- /2 * Rabs (f x)) _ _ (proj2 H1)).
rewrite /norm /= /abs /=.
replace (- / 2 * Rabs (f x) + (g x + / 2 * Rabs (f x))) with (g x) by ring.
apply Rlt_le_trans.
rewrite Rabs_pos_eq.
apply Rmult_lt_reg_l with (1 := Rlt_R0_R2).
replace (2 * (- / 2 * f x + f x)) with (f x) by field.
apply Rle_lt_trans with (2 := H2).
apply Rmax_r.
apply Rlt_le.
apply Rle_lt_trans with (2 := H2).
apply Rmax_l.
-
pose ineq (y : R) := y < Rmin 0 (2 * eps).
assert (Hl: Rbar_locally' m_infty ineq).
now exists (Rmin 0 (2 * eps)).
generalize (filter_and _ (fun (x : T) => ineq (f x)) (Hfg (mkposreal _ pos_half_prf)) (Hf _ Hl)).
apply filter_imp.
simpl.
intros x [H1 H2].
apply HP.
apply Rabs_le_between' in H1.
generalize (Rplus_le_compat_l (/2 * Rabs (f x)) _ _ (proj1 H1)).
rewrite /norm /= /abs /=.
replace (/ 2 * Rabs (f x) + (g x - / 2 * Rabs (f x))) with (g x) by ring.
intros H.
apply Rle_lt_trans with (1 := H).
rewrite Rabs_left.
apply Rmult_lt_reg_l with (1 := Rlt_R0_R2).
replace (2 * (/ 2 * - f x + f x)) with (f x) by field.
apply Rlt_le_trans with (1 := H2).
apply Rmin_r.
apply Rlt_le_trans with (1 := H2).
apply Rmin_l.

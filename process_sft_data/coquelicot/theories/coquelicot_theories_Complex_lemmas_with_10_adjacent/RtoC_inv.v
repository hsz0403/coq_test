Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar.
Require Import Continuity Derive Hierarchy.
Definition C := (R * R)%type.
Definition RtoC (x : R) : C := (x,0).
Coercion RtoC : R >-> C.
Definition Ci : C := (0,1).
Definition Cplus (x y : C) : C := (fst x + fst y, snd x + snd y).
Definition Copp (x : C) : C := (-fst x, -snd x).
Definition Cminus (x y : C) : C := Cplus x (Copp y).
Definition Cmult (x y : C) : C := (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y).
Definition Cinv (x : C) : C := (fst x / (fst x ^ 2 + snd x ^ 2), - snd x / (fst x ^ 2 + snd x ^ 2)).
Definition Cdiv (x y : C) : C := Cmult x (Cinv y).
Delimit Scope C_scope with C.
Local Open Scope C_scope.
Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.
Definition Re (z : C) : R := fst z.
Definition Im (z : C) : R := snd z.
Definition Cmod (x : C) : R := sqrt (fst x ^ 2 + snd x ^ 2).
Definition Cconj (x : C) : C := (fst x, (- snd x)%R).
Definition C_AbelianGroup_mixin := AbelianGroup.Mixin _ _ _ _ Cplus_comm Cplus_assoc Cplus_0_r Cplus_opp_r.
Canonical C_AbelianGroup := AbelianGroup.Pack C C_AbelianGroup_mixin C.
Definition C_Ring_mixin := Ring.Mixin _ _ _ Cmult_assoc Cmult_1_r Cmult_1_l Cmult_plus_distr_r Cmult_plus_distr_l.
Canonical C_Ring := Ring.Pack C (Ring.Class _ _ C_Ring_mixin) C.
Definition C_AbsRing_mixin := AbsRing.Mixin _ _ Cmod_0 Cmod_m1 Cmod_triangle (fun x y => Req_le _ _ (Cmod_mult x y)) Cmod_eq_0.
Canonical C_AbsRing := AbsRing.Pack C (AbsRing.Class _ _ C_AbsRing_mixin) C.
Add Field C_field_field : C_field_theory.
Canonical C_UniformSpace := UniformSpace.Pack C (UniformSpace.class (prod_UniformSpace _ _)) C.
Canonical C_ModuleSpace := ModuleSpace.Pack C_Ring C (ModuleSpace.class _ (Ring_ModuleSpace C_Ring)) C.
Canonical C_NormedModuleAux := NormedModuleAux.Pack C_AbsRing C (NormedModuleAux.Class C_AbsRing _ (ModuleSpace.class _ C_ModuleSpace) (UniformSpace.class C_UniformSpace)) C.
Definition C_NormedModule_mixin := NormedModule.Mixin _ C_NormedModuleAux _ _ Cmod_triangle (fun x y => Req_le _ _ (Cmod_mult x y)) C_NormedModule_mixin_compat1 C_NormedModule_mixin_compat2 Cmod_eq_0.
Canonical C_NormedModule := NormedModule.Pack C_AbsRing C (NormedModule.Class _ _ _ C_NormedModule_mixin) C.
Canonical C_R_ModuleSpace := ModuleSpace.Pack R_Ring C (ModuleSpace.class _ (prod_ModuleSpace R_Ring R_ModuleSpace R_ModuleSpace)) C.
Canonical C_R_NormedModuleAux := NormedModuleAux.Pack R_AbsRing C (NormedModuleAux.Class R_AbsRing _ (ModuleSpace.class _ C_R_ModuleSpace) (UniformSpace.class _)) C.
Canonical C_R_NormedModule := NormedModule.Pack R_AbsRing C (NormedModule.class _ (prod_NormedModule _ _ _)) C.
Definition C_complete_lim (F : (C -> Prop) -> Prop) := (R_complete_lim (fun P => F (fun z => P (Re z))), R_complete_lim (fun P => F (fun z => P (Im z)))).
Definition C_CompleteSpace_mixin := CompleteSpace.Mixin _ C_complete_lim C_complete_ax1 C_complete_ax2.
Canonical C_CompleteNormedModule := CompleteNormedModule.Pack _ C (CompleteNormedModule.Class C_AbsRing _ (NormedModule.class _ C_NormedModule) C_CompleteSpace_mixin) C.
Canonical C_R_CompleteNormedModule := CompleteNormedModule.Pack _ C (CompleteNormedModule.Class R_AbsRing _ (NormedModule.class _ C_R_NormedModule) C_CompleteSpace_mixin) C.
Definition C_lim (f : C -> C) (z : C) : C := (real (Lim (fun x => fst (f (x, snd z))) (fst z)), real (Lim (fun x => snd (f (x, snd z))) (fst z))).
Definition C_derive (f : C -> C) (z : C) := C_lim (fun x => (f x - f z) / (x - z)) z.

Lemma Cmod_1 : Cmod 1 = 1.
Proof.
unfold Cmod.
simpl.
rewrite Rmult_0_l Rplus_0_r 2!Rmult_1_l.
Admitted.

Lemma Cmod_opp : forall x, Cmod (-x) = Cmod x.
Proof.
unfold Cmod.
simpl.
intros x.
apply f_equal.
Admitted.

Lemma Cmod_triangle : forall x y, Cmod (x + y) <= Cmod x + Cmod y.
Proof.
intros x y ; rewrite /Cmod.
apply Rsqr_incr_0_var.
apply Rminus_le_0.
unfold Rsqr ; simpl ; ring_simplify.
rewrite /pow ?Rmult_1_r.
rewrite ?sqrt_sqrt ; ring_simplify.
replace (-2 * fst x * fst y - 2 * snd x * snd y)%R with (- (2 * (fst x * fst y + snd x * snd y)))%R by ring.
rewrite Rmult_assoc -sqrt_mult.
rewrite Rplus_comm.
apply -> Rminus_le_0.
apply Rmult_le_compat_l.
apply Rlt_le, Rlt_0_2.
apply Rsqr_incr_0_var.
apply Rminus_le_0.
rewrite /Rsqr ?sqrt_sqrt ; ring_simplify.
replace (fst x ^ 2 * snd y ^ 2 - 2 * fst x * snd x * fst y * snd y + snd x ^ 2 * fst y ^ 2)%R with ( (fst x * snd y - snd x * fst y)^2)%R by ring.
apply pow2_ge_0.
repeat apply Rplus_le_le_0_compat ; apply Rmult_le_pos ; apply pow2_ge_0.
apply sqrt_pos.
apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
replace (fst x ^ 2 + 2 * fst x * fst y + fst y ^ 2 + snd x ^ 2 + 2 * snd x * snd y + snd y ^ 2)%R with ((fst x + fst y)^2 + (snd x + snd y)^2)%R by ring.
apply Rplus_le_le_0_compat ; apply pow2_ge_0.
apply Rplus_le_le_0_compat ; apply pow2_ge_0.
apply Rplus_le_le_0_compat ; apply pow2_ge_0.
Admitted.

Lemma Cmod_mult : forall x y, Cmod (x * y) = (Cmod x * Cmod y)%R.
Proof.
intros x y.
unfold Cmod.
rewrite -sqrt_mult.
apply f_equal ; simpl ; ring.
apply Rplus_le_le_0_compat ; apply pow2_ge_0.
Admitted.

Lemma Rmax_Cmod : forall x, Rmax (Rabs (fst x)) (Rabs (snd x)) <= Cmod x.
Proof.
case => x y /=.
rewrite -!sqrt_Rsqr_abs.
Admitted.

Lemma Cmod_2Rmax : forall x, Cmod x <= sqrt 2 * Rmax (Rabs (fst x)) (Rabs (snd x)).
Proof.
Admitted.

Lemma RtoC_plus (x y : R) : RtoC (x + y) = RtoC x + RtoC y.
Proof.
unfold RtoC, Cplus ; simpl.
Admitted.

Lemma RtoC_opp (x : R) : RtoC (- x) = - RtoC x.
Proof.
unfold RtoC, Copp ; simpl.
Admitted.

Lemma RtoC_minus (x y : R) : RtoC (x - y) = RtoC x - RtoC y.
Proof.
Admitted.

Lemma RtoC_mult (x y : R) : RtoC (x * y) = RtoC x * RtoC y.
Proof.
unfold RtoC, Cmult ; simpl.
Admitted.

Lemma RtoC_div (x y : R) : (y <> 0)%R -> RtoC (x / y) = RtoC x / RtoC y.
Proof.
intros Hy.
Admitted.

Lemma Cplus_comm (x y : C) : x + y = y + x.
Proof.
Admitted.

Lemma Cplus_assoc (x y z : C) : x + (y + z) = (x + y) + z.
Proof.
Admitted.

Lemma Cplus_0_r (x : C) : x + 0 = x.
Proof.
Admitted.

Lemma Cplus_0_l (x : C) : 0 + x = x.
Proof.
Admitted.

Lemma Cplus_opp_r (x : C) : x + -x = 0.
Proof.
Admitted.

Lemma Copp_plus_distr (z1 z2 : C) : - (z1 + z2) = (- z1 + - z2).
Proof.
Admitted.

Lemma Copp_minus_distr (z1 z2 : C) : - (z1 - z2) = z2 - z1.
Proof.
Admitted.

Lemma Cmult_comm (x y : C) : x * y = y * x.
Proof.
Admitted.

Lemma Cmult_assoc (x y z : C) : x * (y * z) = (x * y) * z.
Proof.
Admitted.

Lemma RtoC_inv (x : R) : (x <> 0)%R -> RtoC (/ x) = / RtoC x.
Proof.
intros Hx.
by apply injective_projections ; simpl ; field.

Require Import Arith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_nat gcd crt sums.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.MuRec Require Import recalg recomp prim_min ra_utils.
Set Implicit Arguments.
Set Default Proof Using "Type".
Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).
Local Notation power := (mscal mult 1).
Opaque ra_cst_n ra_iter_n ra_iter ra_prim_min ra_prim_max.
Opaque ra_plus ra_pred ra_minus ra_mult ra_exp ra_div ra_rem.
Opaque ra_ite ra_eq.
Opaque ra_div2 ra_mod2 ra_pow2 ra_notdiv_pow2.
Section ra_recomp.
Definition ra_decomp_l : recalg 1.
Proof.
apply ra_comp with 2; [ | fill_vec ].
+
apply ra_prim_min.
ra root ra_notdiv_pow2.
*
ra root ra_succ.
ra arg pos0.
*
ra arg pos1.
+
ra root ra_succ.
ra arg pos0.
+
ra root ra_succ.
ra arg pos0.
Defined.
Fact ra_decomp_l_prim_rec : prim_rec ra_decomp_l.
Proof.
ra prim rec.
apply ra_prim_min_prim_rec.
ra prim rec.
Fact ra_decomp_l_val_0 n : ⟦ra_decomp_l⟧ (n##vec_nil) (prim_min (fun i => notdiv_pow2 (S i) (S n)) (S n)).
Proof.
exists (S n##S n##vec_nil); split.
+
apply ra_prim_min_val with (f := fun v i => notdiv_pow2 (S i) (vec_head v)).
intros i v; vec split v with j; vec nil v.
exists (S i##j##vec_nil); split; auto.
pos split; simpl; auto.
exists (i##vec_nil); split; simpl; auto.
pos split; simpl; auto.
+
pos split; simpl; auto; exists (n##vec_nil); split; simpl; auto; pos split; simpl; auto.
Fact ra_decomp_l_rel n : { a | ⟦ra_decomp_l⟧ (n##vec_nil) a /\ divides (power a 2) (S n) /\ ~ divides (power (S a) 2) (S n) }.
Proof.
exists (prim_min (fun i => notdiv_pow2 (S i) (S n)) (S n)); split.
1: {
apply ra_decomp_l_val_0.
}
generalize (prim_min_spec (fun i => notdiv_pow2 (S i) (S n)) (S n)); intros (H1 & H2).
1: {
apply notdiv_pow2_spec_2; intros C.
apply divides_le in C; try discriminate.
generalize (@power_ge_n (S (S n)) 2); intros; lia.
}
apply notdiv_pow2_spec_2 in H1; split; auto.
revert H2; generalize (prim_min (fun i : nat => notdiv_pow2 (S i) (S n)) (S n)); intros [ | k ] Hk.
+
rewrite power_0; apply divides_1.
+
apply notdiv_pow2_spec_1, Hk; lia.
Hint Resolve ra_decomp_l_prim_rec : core.
Opaque ra_decomp_l.
Definition ra_decomp_r : recalg 1.
Proof.
ra root ra_div.
+
ra root ra_succ.
ra arg pos0.
+
ra root ra_pow2.
ra root ra_succ.
ra root ra_decomp_l.
ra arg pos0.
Defined.
Fact ra_decomp_r_prim_rec : prim_rec ra_decomp_r.
Proof.
ra prim rec.
Fact ra_decomp_r_rel n : { b | ⟦ra_decomp_r⟧ (n##vec_nil) b /\ exists a, ⟦ra_decomp_l⟧ (n##vec_nil) a /\ S n = power a 2 * (2*b+1) }.
Proof.
destruct (ra_decomp_l_rel n) as (a & H1 & H2 & H3).
exists (div (S n) (power (S a) 2)); split.
+
exists (S n##power (S a) 2##vec_nil); split.
{
apply ra_div_val; generalize (@power_ge_1 (S a) 2); intros; lia.
}
pos split; simpl; auto.
*
exists (n##vec_nil); split; simpl; auto.
pos split; simpl; auto.
*
exists (S a##vec_nil); split; auto.
pos split; simpl; auto.
exists (a##vec_nil); split; simpl; auto.
pos split; simpl; auto.
exists (n##vec_nil); split; auto.
pos split; simpl; auto.
+
exists a; split; auto.
generalize (div_rem_spec1 (S n) (power a 2)).
apply divides_rem_eq in H2; rewrite H2, Nat.add_0_r.
rewrite power_S in *.
clear H1; revert H2 H3.
generalize (S n) (power a 2) (power2_gt_0 a); clear n a; intros n p H1 H2 H3 H4.
rewrite H4 at 1; rewrite mult_comm; f_equal.
rewrite divides_rem_eq in H3.
rewrite (mult_comm _ p), div_mult; try lia.
rewrite mult_comm, rem_mult in H3; try lia.
rewrite (@div_rem_spec1 (div n p) 2) at 1.
rewrite H2 in H3; simpl in H3.
generalize (@div_rem_spec2 (div n p) 2); intros H5.
rewrite mult_comm in H3.
destruct (rem (div n p) 2) as [ | [ | ] ]; lia.
Fact ra_decomp_lr_val n : ⟦ra_decomp_l⟧ (n##vec_nil) (decomp_l n) /\ ⟦ra_decomp_r⟧ (n##vec_nil) (decomp_r n).
Proof.
destruct (ra_decomp_r_rel n) as (b & H1 & a & H2 & H3).
rewrite (decomp_lr_spec n) in H3.
apply decomp_uniq in H3; destruct H3; subst a b; auto.
Fact ra_decomp_l_val n : ⟦ra_decomp_l⟧ (n##vec_nil) (decomp_l n).
Proof.
apply ra_decomp_lr_val.
Fact ra_decomp_r_val n : ⟦ra_decomp_r⟧ (n##vec_nil) (decomp_r n).
Proof.
apply ra_decomp_lr_val.
Definition ra_recomp : recalg 2.
Proof.
ra root ra_pred.
ra root ra_mult.
+
ra root ra_pow2.
ra arg pos0.
+
ra root ra_succ.
ra root ra_mult.
*
ra cst 2.
*
ra arg pos1.
Defined.
Fact ra_recomp_prim_rec : prim_rec ra_recomp.
Proof.
ra prim rec.
Fact ra_recomp_val a b : ⟦ra_recomp⟧ (a##b##vec_nil) (recomp a b).
Proof.
unfold recomp.
rewrite plus_comm.
exists (power a 2 * (S (2*b)) ## vec_nil); split; auto.
pos split; simpl.
exists (power a 2##S (2*b)##vec_nil); split; auto.
pos split; simpl; auto.
+
exists (a##vec_nil); split; auto.
pos split; simpl; auto.
+
exists (2*b##vec_nil); split; simpl; auto.
pos split; simpl; auto.
exists (2##b##vec_nil); split; auto.
{
apply ra_mult_val.
}
pos split; simpl; auto.
End ra_recomp.
Hint Resolve ra_decomp_l_prim_rec ra_decomp_r_prim_rec ra_recomp_prim_rec ra_decomp_l_val ra_decomp_r_val ra_recomp_val : core.
Opaque ra_decomp_l ra_decomp_r ra_recomp.
Section ra_inject_project.
Fixpoint ra_inject n : recalg n.
Proof.
destruct n as [ | n ].
+
ra cst 0.
+
ra root ra_recomp.
*
ra arg pos0.
*
apply ra_comp with (1 := ra_inject n).
apply vec_set_pos.
intros p; apply ra_proj, pos_nxt, p.
Defined.
Fact ra_inject_prim_rec n : prim_rec (ra_inject n).
Proof.
induction n as [ | n IHn ]; simpl; split; auto.
+
pos split.
+
pos split; ra prim rec.
intro; vec pos simpl.
Fact ra_inject_val n v : ⟦ra_inject n⟧ v (inject v).
Proof.
induction n as [ | n IHn ]; simpl.
+
vec nil v; simpl; auto.
+
vec split v with x.
exists (x##inject v##vec_nil); split.
*
apply ra_recomp_val.
*
pos split; simpl; auto.
exists v; split; auto.
intro; vec pos simpl.
Fixpoint ra_project n (p : pos n) : recalg 1 := match p with | pos_fst => ra_decomp_l | pos_nxt p => ra_comp (ra_project p) (ra_decomp_r##vec_nil) end.
Fact ra_project_prim_rec n p : prim_rec (@ra_project n p).
Proof.
induction p as [ | n p IHp ]; simpl; auto; split; auto.
pos split; auto.
Fact ra_project_val n p x : ⟦@ra_project n p⟧ (x##vec_nil) (vec_pos (@project n x) p).
Proof.
revert x; induction p as [ | n p IHp ]; intros x; simpl; auto.
exists (decomp_r x##vec_nil); split.
+
apply IHp.
+
pos split; simpl; auto.
Fact ra_project_rel n p v x : ⟦@ra_project n p⟧ v x <-> x = vec_pos (@project n (vec_head v)) p.
Proof.
vec split v with a; vec nil v.
split.
+
intros H; apply ra_rel_fun with (1 := H), ra_project_val.
+
intros; subst; apply ra_project_val.
Definition ra_vec_project n : vec (recalg 1) n.
Proof.
apply vec_set_pos, ra_project.
Defined.
End ra_inject_project.
Hint Resolve ra_project_prim_rec ra_inject_prim_rec ra_project_val ra_inject_val : core.

Fact ra_decomp_lr_val n : ⟦ra_decomp_l⟧ (n##vec_nil) (decomp_l n) /\ ⟦ra_decomp_r⟧ (n##vec_nil) (decomp_r n).
Proof.
destruct (ra_decomp_r_rel n) as (b & H1 & a & H2 & H3).
rewrite (decomp_lr_spec n) in H3.
Admitted.

Fact ra_decomp_l_val n : ⟦ra_decomp_l⟧ (n##vec_nil) (decomp_l n).
Proof.
Admitted.

Fact ra_decomp_r_val n : ⟦ra_decomp_r⟧ (n##vec_nil) (decomp_r n).
Proof.
Admitted.

Definition ra_recomp : recalg 2.
Proof.
ra root ra_pred.
ra root ra_mult.
+
ra root ra_pow2.
ra arg pos0.
+
ra root ra_succ.
ra root ra_mult.
*
ra cst 2.
*
Admitted.

Fact ra_recomp_prim_rec : prim_rec ra_recomp.
Proof.
Admitted.

Fact ra_recomp_val a b : ⟦ra_recomp⟧ (a##b##vec_nil) (recomp a b).
Proof.
unfold recomp.
rewrite plus_comm.
exists (power a 2 * (S (2*b)) ## vec_nil); split; auto.
pos split; simpl.
exists (power a 2##S (2*b)##vec_nil); split; auto.
pos split; simpl; auto.
+
exists (a##vec_nil); split; auto.
pos split; simpl; auto.
+
exists (2*b##vec_nil); split; simpl; auto.
pos split; simpl; auto.
exists (2##b##vec_nil); split; auto.
{
apply ra_mult_val.
}
Admitted.

Fixpoint ra_inject n : recalg n.
Proof.
destruct n as [ | n ].
+
ra cst 0.
+
ra root ra_recomp.
*
ra arg pos0.
*
apply ra_comp with (1 := ra_inject n).
apply vec_set_pos.
Admitted.

Fact ra_inject_prim_rec n : prim_rec (ra_inject n).
Proof.
induction n as [ | n IHn ]; simpl; split; auto.
+
pos split.
+
pos split; ra prim rec.
Admitted.

Fact ra_inject_val n v : ⟦ra_inject n⟧ v (inject v).
Proof.
induction n as [ | n IHn ]; simpl.
+
vec nil v; simpl; auto.
+
vec split v with x.
exists (x##inject v##vec_nil); split.
*
apply ra_recomp_val.
*
pos split; simpl; auto.
exists v; split; auto.
Admitted.

Fact ra_project_prim_rec n p : prim_rec (@ra_project n p).
Proof.
induction p as [ | n p IHp ]; simpl; auto; split; auto.
Admitted.

Fact ra_project_rel n p v x : ⟦@ra_project n p⟧ v x <-> x = vec_pos (@project n (vec_head v)) p.
Proof.
vec split v with a; vec nil v.
split.
+
intros H; apply ra_rel_fun with (1 := H), ra_project_val.
+
Admitted.

Definition ra_vec_project n : vec (recalg 1) n.
Proof.
Admitted.

Fact ra_project_val n p x : ⟦@ra_project n p⟧ (x##vec_nil) (vec_pos (@project n x) p).
Proof.
revert x; induction p as [ | n p IHp ]; intros x; simpl; auto.
exists (decomp_r x##vec_nil); split.
+
apply IHp.
+
pos split; simpl; auto.

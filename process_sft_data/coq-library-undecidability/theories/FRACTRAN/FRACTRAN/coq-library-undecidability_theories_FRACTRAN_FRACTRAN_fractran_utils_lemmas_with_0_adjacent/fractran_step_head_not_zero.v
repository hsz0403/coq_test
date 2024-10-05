Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils_tac utils_list utils_nat gcd rel_iter pos vec.
Require Import Undecidability.FRACTRAN.FRACTRAN.
Set Implicit Arguments.
Section fractran_utils.
Implicit Type l : list (nat*nat).
Fact fractran_step_nil_inv x y : nil /F/ x → y <-> False.
Proof.
split; inversion 1.
Fact fractran_step_cons_inv p q l x y : (p,q)::l /F/ x → y <-> q*y = p*x \/ ~ divides q (p*x) /\ l /F/ x → y.
Proof.
split.
+
inversion 1; auto.
+
intros [ H | (H1 & H2) ]; [ constructor 1 | constructor 2 ]; auto.
Fact mul_pos_inj_l q x y : q <> 0 -> q*x = q*y -> x = y.
Proof.
intros H1 H2.
destruct q; try lia.
apply le_antisym; apply mult_S_le_reg_l with q; lia.
Fact fractan_stop_nil_inv x : fractran_stop nil x <-> True.
Proof.
split; try tauto; intros _ z; rewrite fractran_step_nil_inv; tauto.
Fact fractan_stop_cons_inv p q l x : fractran_stop ((p,q)::l) x <-> ~ divides q (p*x) /\ fractran_stop l x.
Proof.
split.
*
intros H.
assert (~ divides q (p*x)) as H'.
{
intros (z & Hz); apply (H z); constructor; rewrite Hz; ring.
}
split; auto.
intros z Hz; apply (H z); constructor 2; auto.
*
intros (H1 & H2) z Hz.
apply fractran_step_cons_inv in Hz.
destruct Hz as [ H3 | (H3 & H4) ].
-
apply H1; exists z; rewrite <- H3; ring.
-
apply (H2 _ H4).
Fact fractran_step_dec l x : { y | l /F/ x → y } + { fractran_stop l x }.
Proof.
induction l as [ | (a,b) l IH ].
+
right; rewrite fractan_stop_nil_inv; auto.
+
destruct (divides_dec (a*x) b) as [ (y & Hy) | ].
*
left; exists y; constructor 1; rewrite Hy; ring.
*
destruct IH as [ (y & ?) | ].
-
left; exists y; now constructor 2.
-
right; apply fractan_stop_cons_inv; auto.
Let remove_zero_den l := filter (fun c => if eq_nat_dec (snd c) 0 then false else true) l.
Let remove_zero_den_Forall l : fractran_regular (remove_zero_den l).
Proof.
unfold fractran_regular.
induction l as [ | (p,q) ]; simpl; auto.
destruct (eq_nat_dec q 0); auto.
Section zero_cases.
Fact fractran_zero_num_step l : Exists (fun c => fst c = 0) l -> forall x, exists y, l /F/ x → y.
Proof.
induction 1 as [ (p,q) l Hl | (p,q) l Hl IHl ]; simpl in Hl.
+
intros x; exists 0; subst; constructor; lia.
+
intros x.
destruct (divides_dec (p*x) q) as [ (y & Hy) | C ].
*
exists y; constructor; rewrite Hy, mult_comm; auto.
*
destruct (IHl x) as (y & Hy); exists y; constructor 2; auto.
Fact fractran_step_head_not_zero p q l y : q <> 0 -> (p,q)::l /F/ 0 → y -> y = 0.
Proof.
intros H2 H3.
apply fractran_step_cons_inv in H3.
destruct H3 as [ H3 | (H3 & _) ].
+
rewrite Nat.mul_0_r in H3; apply mult_is_O in H3; lia.
+
destruct H3; exists 0; ring.
Fact fractran_rt_head_not_zero p q l n y : q <> 0 -> fractran_steps ((p,q)::l) n 0 y -> y = 0.
Proof.
intros H2.
induction n as [ | n IHn ].
+
simpl; auto.
+
intros (a & H3 & H4).
apply fractran_step_head_not_zero in H3; subst; auto.
Fact fractran_step_no_zero_den l x y : fractran_regular l -> l /F/ x → y -> x = 0 -> y = 0.
Proof.
unfold fractran_regular.
intros H1 H2; revert H2 H1.
induction 1 as [ p q l x y H | p q l x y H1 H2 IH2 ]; rewrite Forall_cons_inv; simpl; intros (H3 & H4) ?; subst.
+
rewrite Nat.mul_0_r in H; apply mult_is_O in H; lia.
+
destruct H1; exists 0; ring.
Fact fractran_step_no_zero_num l : Forall (fun c => fst c <> 0) l -> forall x y, l /F/ x → y -> y = 0 -> x = 0.
Proof.
intros H1 x y H2; revert H2 H1.
induction 1 as [ p q l x y H1 | p q l x y H1 H2 IH2 ]; intros H3; rewrite Forall_cons_inv in H3; simpl in H3; destruct H3 as (H3 & H4); auto.
intros; subst y; rewrite Nat.mul_0_r in H1; symmetry in H1; apply mult_is_O in H1; lia.
Fact fractran_rt_no_zero_den l n y : fractran_regular l -> fractran_steps l n 0 y -> y = 0.
Proof.
intros H; induction n as [ | n IHn ].
+
simpl; auto.
+
intros (x & H1 & H2).
apply fractran_step_no_zero_den with (1 := H) in H1; subst; auto.
Fact fractran_rt_no_zero_num l : Forall (fun c => fst c <> 0) l -> forall n x, fractran_steps l n x 0 -> x = 0.
Proof.
intros H; induction n as [ | n IHn ]; intros x; simpl; auto.
intros (y & H1 & H2).
apply IHn in H2.
revert H1 H2; apply fractran_step_no_zero_num; auto.
Fact fractran_zero_num l x : Exists (fun c => fst c = 0) l -> exists y, l /F/ x → y.
Proof.
induction 1 as [ (p,q) l | (p,q) l Hl IHl ]; simpl in *.
+
exists 0; constructor 1; subst; ring.
+
destruct (divides_dec (p*x) q) as [ (y & Hy) | H ].
*
exists y; constructor 1; rewrite Hy; ring.
*
destruct IHl as (y & Hy); exists y; constructor 2; auto.
End zero_cases.
Fact FRACTAN_cases ll : { Exists (fun c => fst c = 0) ll } + { Forall (fun c => snd c <> 0) ll } + { p : nat & { mm | Forall (fun c => fst c <> 0) ll /\ Exists (fun c => snd c = 0) ll /\ ll = (p,0):: mm /\ p <> 0 } } + { p : nat & { q : nat & { mm | Forall (fun c => fst c <> 0) ll /\ Exists (fun c => snd c = 0) ll /\ ll = (p,q):: mm /\ q <> 0 /\ p <> 0 } } }.
Proof.
destruct (Forall_Exists_dec (fun c : nat * nat => snd c <> 0)) with (l := ll) as [ ? | Hl1 ]; auto.
{
intros (p, q); destruct (eq_nat_dec q 0); simpl; subst; [ right | left]; lia.
}
assert (Exists (fun c => snd c = 0) ll) as H1.
{
revert Hl1; induction 1; [ constructor 1 | constructor 2 ]; auto; lia.
}
clear Hl1.
destruct (Forall_Exists_dec (fun c : nat * nat => fst c <> 0)) with (l := ll) as [ Hl3 | Hl3 ].
{
intros (p, q); destruct (eq_nat_dec p 0); simpl; subst; [ right | left ]; lia.
}
2: {
do 3 left; clear H1; revert Hl3; induction 1; [ constructor 1 | constructor 2 ]; auto; lia.
}
case_eq ll.
{
intro; subst; exfalso; inversion H1.
}
intros (p,q) mm Hll.
destruct (eq_nat_dec p 0) as [ Hp | Hp ].
{
subst; rewrite Forall_cons_inv in Hl3; simpl in Hl3; lia.
}
destruct q.
+
left; right; exists p, mm; subst; auto.
+
right; exists p, (S q), mm; subst; repeat (split; auto).
End fractran_utils.

Fact fractran_step_head_not_zero p q l y : q <> 0 -> (p,q)::l /F/ 0 → y -> y = 0.
Proof.
intros H2 H3.
apply fractran_step_cons_inv in H3.
destruct H3 as [ H3 | (H3 & _) ].
+
rewrite Nat.mul_0_r in H3; apply mult_is_O in H3; lia.
+
destruct H3; exists 0; ring.

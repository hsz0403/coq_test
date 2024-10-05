Require Import List Arith Lia Eqdep_dec Bool.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations decidable fol_ops membership hfs.
Set Implicit Arguments.
Section bt_model_n.
Variable (X : Type) (Xfin : finite_t X) (Xdiscr : discrete X) (x0 : X) (nt : nat).
Infix "∈" := hfs_mem.
Notation "x ⊆ y" := (forall u, u ∈ x -> u ∈ y).
Notation "⟬ x , y ⟭" := (hfs_opair x y).
Let X_surj_hfs : { l : hfs & { f : hfs -> X & { g : X -> hfs | hfs_transitive l /\ hfs_empty ∈ l /\ (forall p, g p ∈ l) /\ (forall x, x ∈ l -> exists p, x = g p) /\ (forall p, f (g p) = p) } } }.
Proof.
destruct (finite_t_discrete_bij_t_pos Xfin) as ([ | n ] & Hn); auto.
1: {
exfalso; destruct Hn as (f & g & H1 & H2).
generalize (f x0); intro p; invert pos p.
}
destruct Hn as (f & g & H1 & H2).
destruct (hfs_pos_n_transitive n) as (l & g' & f' & G1 & G0 & G2 & G3 & G4).
exists l, (fun x => g (g' x)), (fun x => f' (f x)); msplit 4; auto.
+
intros x Hx.
destruct (G3 x Hx) as (p & Hp).
exists (g p); rewrite H2; auto.
+
intros p; rewrite G4; auto.
Let l := projT1 X_surj_hfs.
Let s := projT1 (projT2 X_surj_hfs).
Let i := proj1_sig (projT2 (projT2 (X_surj_hfs))).
Let Hl : hfs_transitive l.
Proof.
apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))).
Let Hempty : hfs_empty ∈ l.
Proof.
apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))).
Let Hs : forall x, s (i x) = x.
Proof.
apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))).
Let Hi : forall x, i x ∈ l.
Proof.
apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))).
Let Hi' : forall s, s ∈ l -> exists x, s = i x.
Proof.
apply (proj2_sig (projT2 (projT2 (X_surj_hfs)))).
Let p := iter hfs_pow l (1+(2*nt)).
Let Hp1 : hfs_transitive p.
Proof.
apply hfs_iter_pow_trans; auto.
Let Hp2 : l ∈ p.
Proof.
apply hfs_iter_pow_le with (n := 1); simpl; auto; try lia.
apply hfs_pow_spec; auto.
Let Hp5 n v : (forall p, vec_pos v p ∈ l) -> @hfs_tuple n v ∈ iter hfs_pow l (2*n).
Proof.
apply hfs_tuple_pow; auto.
Let Hp6 n v : n <= nt -> (forall p, vec_pos v p ∈ l) -> @hfs_tuple n v ∈ p.
Proof.
intros L H; apply Hp5 in H.
revert H; apply hfs_iter_pow_le; try lia; auto.
Variable (R : vec X nt -> Prop).
Hypothesis HR : forall v, { R v } + { ~ R v }.
Hint Resolve finite_t_prod hfs_mem_fin_t : core.
Let encode_R : { r | r ∈ p /\ (forall v, @hfs_tuple nt v ∈ r -> forall q, vec_pos v q ∈ l) /\ forall v, R v <-> hfs_tuple (vec_map i v) ∈ r }.
Proof.
set (P v := R (vec_map s v) /\ forall q, vec_pos v q ∈ l).
set (f := @hfs_tuple nt).
destruct hfs_comprehension with (P := P) (f := f) as (r & Hr).
+
apply fin_t_dec.
*
intros; apply HR.
*
apply fin_t_vec with (P := fun t => t ∈ l).
apply hfs_mem_fin_t.
+
exists r; msplit 2.
*
unfold p; rewrite plus_comm, iter_plus with (b := 1).
apply hfs_pow_spec; intros x; rewrite Hr.
intros (v & H1 & <-).
apply Hp5, H1.
*
unfold f; intros v.
rewrite Hr.
intros (w & H1 & H2).
apply hfs_tuple_spec in H2; subst w.
apply H1.
*
intros v.
rewrite Hr.
split.
-
exists (vec_map i v); split; auto.
split; auto.
++
rewrite vec_map_map.
revert H; apply fol_equiv_ext.
f_equal; apply vec_pos_ext; intro; rew vec.
++
intro; rew vec.
-
intros (w & (H1 & _) & H2).
apply hfs_tuple_spec in H2.
revert H1; subst w; apply fol_equiv_ext.
f_equal; apply vec_pos_ext; intro; rew vec.
Let r := proj1_sig encode_R.
Let Hr1 : r ∈ p.
Proof.
apply (proj2_sig encode_R).
Let Hr2 v : @hfs_tuple nt v ∈ r -> forall q, vec_pos v q ∈ l.
Proof.
apply (proj2_sig encode_R).
Let Hr3 v : R v <-> hfs_tuple (vec_map i v) ∈ r.
Proof.
apply (proj2_sig encode_R).
Let p_bool x := if hfs_mem_dec x p then true else false.
Let p_bool_spec x : x ∈ p <-> p_bool x = true.
Proof.
unfold p_bool.
destruct (hfs_mem_dec x p); split; try tauto; discriminate.
Let Y := sig (fun x => p_bool x = true).
Let eqY : forall x y : Y, proj1_sig x = proj1_sig y -> x = y.
Proof.
intros (x & Hx) (y & Hy); simpl.
intros; subst; f_equal; apply UIP_dec, bool_dec.
Let HY : finite_t Y.
Proof.
apply fin_t_finite_t.
+
intros; apply UIP_dec, bool_dec.
+
generalize (hfs_mem_fin_t p); apply fin_t_equiv.
intros x; auto.
Let discrY : discrete Y.
Proof.
intros (x & Hx) (y & Hy).
destruct (hfs_eq_dec x y) as [ -> | D ].
+
left; f_equal; apply UIP_dec, bool_dec.
+
right; contradict D; inversion D; auto.
Let mem (x y : Y) := proj1_sig x ∈ proj1_sig y.
Let mem_dec : forall x y, { mem x y } + { ~ mem x y }.
Proof.
intros (a & ?) (b & ?); unfold mem; simpl; apply hfs_mem_dec.
Let yl : Y.
Proof.
exists l; apply p_bool_spec, Hp2.
Defined.
Let yr : Y.
Proof.
exists r; apply p_bool_spec, Hr1.
Defined.
Let is_equiv : forall x y, mb_equiv mem x y <-> proj1_sig x = proj1_sig y.
Proof.
intros (x & Hx) (y & Hy); simpl.
unfold mb_equiv, mem; simpl; split.
2: intros []; tauto.
intros H.
apply hfs_mem_ext.
intros z; split; intros Hz.
*
apply p_bool_spec in Hx.
generalize (Hp1 Hz Hx).
rewrite p_bool_spec; intros H'.
apply (H (exist _ z H')); auto.
*
apply p_bool_spec in Hy.
generalize (Hp1 Hz Hy).
rewrite p_bool_spec; intros H'.
apply (H (exist _ z H')); auto.
Let is_pair : forall x y k, mb_is_pair mem k x y <-> proj1_sig k = hfs_pair (proj1_sig x) (proj1_sig y).
Proof.
intros (x & Hx) (y & Hy) (k & Hk); simpl.
unfold mb_is_pair; simpl; rewrite hfs_mem_ext.
generalize Hx Hy Hk; revert Hx Hy Hk.
do 3 rewrite <- p_bool_spec at 1.
intros Hx' Hy' Hk' Hx Hy Hk.
split.
+
intros H a; split; rewrite hfs_pair_spec; [ intros Ha | intros [ Ha | Ha ] ].
*
generalize (Hp1 Ha Hk'); rewrite p_bool_spec; intros Ha'.
specialize (H (exist _ a Ha')); simpl in H.
repeat rewrite is_equiv in H; apply H; auto.
*
subst; apply (H (exist _ x Hx)); repeat rewrite is_equiv; simpl; auto.
*
subst; apply (H (exist _ y Hy)); repeat rewrite is_equiv; simpl; auto.
+
intros H (a & Ha); repeat rewrite is_equiv; simpl; rewrite <- hfs_pair_spec.
apply H.
Let is_opair : forall x y k, mb_is_opair mem k x y <-> proj1_sig k = ⟬proj1_sig x,proj1_sig y⟭.
Proof.
intros (x & Hx) (y & Hy) (k & Hk); simpl.
unfold mb_is_opair; split.
+
intros ((a & Ha) & (b & Hb) & H); revert H.
repeat rewrite is_pair; simpl.
intros (-> & -> & ->); auto.
+
intros ->.
generalize Hx Hy Hk; revert Hx Hy Hk.
do 3 rewrite <- p_bool_spec at 1.
intros Hx' Hy' Hk' Hx Hy Hk.
apply hfs_trans_opair_inv in Hk'; auto.
do 2 rewrite p_bool_spec in Hk'.
destruct Hk' as (H1 & H2).
exists (exist _ (hfs_pair x x) H1).
exists (exist _ (hfs_pair x y) H2).
repeat rewrite is_pair; simpl; auto.
Let is_tuple n : forall v t, @mb_is_tuple _ mem t n v <-> proj1_sig t = hfs_tuple (vec_map (@proj1_sig _ _) v).
Proof.
induction n as [ | n IHn ]; intros v (t & Ht).
+
vec nil v; clear v; simpl; split.
*
intros H; apply hfs_mem_ext.
intros z; split.
-
intros Hz.
assert (Hz' : p_bool z = true).
{
apply p_bool_spec.
apply Hp1 with (1 := Hz), p_bool_spec; auto.
}
destruct (H (exist _ z Hz')); auto.
-
rewrite hfs_empty_spec; tauto.
*
intros -> (z & ?); unfold mem; simpl.
rewrite hfs_empty_spec; tauto.
+
vec split v with x; simpl; split.
*
intros (t' & H1 & H2).
rewrite IHn in H2; try lia.
rewrite <- H2.
apply is_opair with (k := exist _ t Ht); auto.
*
intros ->.
assert (H1 : p_bool (hfs_tuple (vec_map (@proj1_sig _ _) v)) = true).
{
apply p_bool_spec.
apply p_bool_spec in Ht.
apply hfs_trans_opair_inv, proj2, hfs_trans_pair_inv in Ht; tauto.
}
exists (exist _ (hfs_tuple (vec_map (@proj1_sig _ _) v)) H1); split.
-
rewrite is_opair; simpl; auto.
-
rewrite IHn; simpl; auto.
Let has_tuples : mb_has_tuples mem yl nt.
Proof.
intros v Hv.
set (t := hfs_tuple (vec_map (proj1_sig (P:=fun x : hfs => p_bool x = true)) v)).
assert (H1 : p_bool t = true).
{
apply p_bool_spec, Hp6; auto; intro; rew vec; apply Hv.
}
exists (exist _ t H1).
apply is_tuple; simpl; reflexivity.
Let i' : X -> Y.
Proof.
intros x.
exists (i x).
apply p_bool_spec.
generalize (Hi x) Hp2; apply Hp1.
Defined.
Let Hi'' x : mem (i' x) yl.
Proof.
unfold i', yl, mem; simpl; auto.
Let s' (y : Y) : X := s (proj1_sig y).
End bt_model_n.

Let X_surj_hfs : { l : hfs & { f : hfs -> X & { g : X -> hfs | hfs_transitive l /\ hfs_empty ∈ l /\ (forall p, g p ∈ l) /\ (forall x, x ∈ l -> exists p, x = g p) /\ (forall p, f (g p) = p) } } }.
Proof.
destruct (finite_t_discrete_bij_t_pos Xfin) as ([ | n ] & Hn); auto.
1: {
exfalso; destruct Hn as (f & g & H1 & H2).
generalize (f x0); intro p; invert pos p.
}
destruct Hn as (f & g & H1 & H2).
destruct (hfs_pos_n_transitive n) as (l & g' & f' & G1 & G0 & G2 & G3 & G4).
exists l, (fun x => g (g' x)), (fun x => f' (f x)); msplit 4; auto.
+
intros x Hx.
destruct (G3 x Hx) as (p & Hp).
exists (g p); rewrite H2; auto.
+
Admitted.

Let Hl : hfs_transitive l.
Proof.
Admitted.

Let Hempty : hfs_empty ∈ l.
Proof.
Admitted.

Let Hs : forall x, s (i x) = x.
Proof.
Admitted.

Let Hi : forall x, i x ∈ l.
Proof.
Admitted.

Let Hi' : forall s, s ∈ l -> exists x, s = i x.
Proof.
Admitted.

Let Hp1 : hfs_transitive p.
Proof.
Admitted.

Let Hp2 : l ∈ p.
Proof.
apply hfs_iter_pow_le with (n := 1); simpl; auto; try lia.
Admitted.

Let Hp5 n v : (forall p, vec_pos v p ∈ l) -> @hfs_tuple n v ∈ iter hfs_pow l (2*n).
Proof.
Admitted.

Let Hp6 n v : n <= nt -> (forall p, vec_pos v p ∈ l) -> @hfs_tuple n v ∈ p.
Proof.
intros L H; apply Hp5 in H.
Admitted.

Let encode_R : { r | r ∈ p /\ (forall v, @hfs_tuple nt v ∈ r -> forall q, vec_pos v q ∈ l) /\ forall v, R v <-> hfs_tuple (vec_map i v) ∈ r }.
Proof.
set (P v := R (vec_map s v) /\ forall q, vec_pos v q ∈ l).
set (f := @hfs_tuple nt).
destruct hfs_comprehension with (P := P) (f := f) as (r & Hr).
+
apply fin_t_dec.
*
intros; apply HR.
*
apply fin_t_vec with (P := fun t => t ∈ l).
apply hfs_mem_fin_t.
+
exists r; msplit 2.
*
unfold p; rewrite plus_comm, iter_plus with (b := 1).
apply hfs_pow_spec; intros x; rewrite Hr.
intros (v & H1 & <-).
apply Hp5, H1.
*
unfold f; intros v.
rewrite Hr.
intros (w & H1 & H2).
apply hfs_tuple_spec in H2; subst w.
apply H1.
*
intros v.
rewrite Hr.
split.
-
exists (vec_map i v); split; auto.
split; auto.
++
rewrite vec_map_map.
revert H; apply fol_equiv_ext.
f_equal; apply vec_pos_ext; intro; rew vec.
++
intro; rew vec.
-
intros (w & (H1 & _) & H2).
apply hfs_tuple_spec in H2.
revert H1; subst w; apply fol_equiv_ext.
Admitted.

Let Hr1 : r ∈ p.
Proof.
Admitted.

Let Hr2 v : @hfs_tuple nt v ∈ r -> forall q, vec_pos v q ∈ l.
Proof.
Admitted.

Let Hr3 v : R v <-> hfs_tuple (vec_map i v) ∈ r.
Proof.
Admitted.

Let p_bool_spec x : x ∈ p <-> p_bool x = true.
Proof.
unfold p_bool.
Admitted.

Let eqY : forall x y : Y, proj1_sig x = proj1_sig y -> x = y.
Proof.
intros (x & Hx) (y & Hy); simpl.
Admitted.

Let HY : finite_t Y.
Proof.
apply fin_t_finite_t.
+
intros; apply UIP_dec, bool_dec.
+
generalize (hfs_mem_fin_t p); apply fin_t_equiv.
Admitted.

Let discrY : discrete Y.
Proof.
intros (x & Hx) (y & Hy).
destruct (hfs_eq_dec x y) as [ -> | D ].
+
left; f_equal; apply UIP_dec, bool_dec.
+
Admitted.

Let mem_dec : forall x y, { mem x y } + { ~ mem x y }.
Proof.
Admitted.

Let yr : Y.
Proof.
Admitted.

Let is_equiv : forall x y, mb_equiv mem x y <-> proj1_sig x = proj1_sig y.
Proof.
intros (x & Hx) (y & Hy); simpl.
unfold mb_equiv, mem; simpl; split.
2: intros []; tauto.
intros H.
apply hfs_mem_ext.
intros z; split; intros Hz.
*
apply p_bool_spec in Hx.
generalize (Hp1 Hz Hx).
rewrite p_bool_spec; intros H'.
apply (H (exist _ z H')); auto.
*
apply p_bool_spec in Hy.
generalize (Hp1 Hz Hy).
rewrite p_bool_spec; intros H'.
Admitted.

Let is_pair : forall x y k, mb_is_pair mem k x y <-> proj1_sig k = hfs_pair (proj1_sig x) (proj1_sig y).
Proof.
intros (x & Hx) (y & Hy) (k & Hk); simpl.
unfold mb_is_pair; simpl; rewrite hfs_mem_ext.
generalize Hx Hy Hk; revert Hx Hy Hk.
do 3 rewrite <- p_bool_spec at 1.
intros Hx' Hy' Hk' Hx Hy Hk.
split.
+
intros H a; split; rewrite hfs_pair_spec; [ intros Ha | intros [ Ha | Ha ] ].
*
generalize (Hp1 Ha Hk'); rewrite p_bool_spec; intros Ha'.
specialize (H (exist _ a Ha')); simpl in H.
repeat rewrite is_equiv in H; apply H; auto.
*
subst; apply (H (exist _ x Hx)); repeat rewrite is_equiv; simpl; auto.
*
subst; apply (H (exist _ y Hy)); repeat rewrite is_equiv; simpl; auto.
+
intros H (a & Ha); repeat rewrite is_equiv; simpl; rewrite <- hfs_pair_spec.
Admitted.

Let is_opair : forall x y k, mb_is_opair mem k x y <-> proj1_sig k = ⟬proj1_sig x,proj1_sig y⟭.
Proof.
intros (x & Hx) (y & Hy) (k & Hk); simpl.
unfold mb_is_opair; split.
+
intros ((a & Ha) & (b & Hb) & H); revert H.
repeat rewrite is_pair; simpl.
intros (-> & -> & ->); auto.
+
intros ->.
generalize Hx Hy Hk; revert Hx Hy Hk.
do 3 rewrite <- p_bool_spec at 1.
intros Hx' Hy' Hk' Hx Hy Hk.
apply hfs_trans_opair_inv in Hk'; auto.
do 2 rewrite p_bool_spec in Hk'.
destruct Hk' as (H1 & H2).
exists (exist _ (hfs_pair x x) H1).
exists (exist _ (hfs_pair x y) H2).
Admitted.

Let is_tuple n : forall v t, @mb_is_tuple _ mem t n v <-> proj1_sig t = hfs_tuple (vec_map (@proj1_sig _ _) v).
Proof.
induction n as [ | n IHn ]; intros v (t & Ht).
+
vec nil v; clear v; simpl; split.
*
intros H; apply hfs_mem_ext.
intros z; split.
-
intros Hz.
assert (Hz' : p_bool z = true).
{
apply p_bool_spec.
apply Hp1 with (1 := Hz), p_bool_spec; auto.
}
destruct (H (exist _ z Hz')); auto.
-
rewrite hfs_empty_spec; tauto.
*
intros -> (z & ?); unfold mem; simpl.
rewrite hfs_empty_spec; tauto.
+
vec split v with x; simpl; split.
*
intros (t' & H1 & H2).
rewrite IHn in H2; try lia.
rewrite <- H2.
apply is_opair with (k := exist _ t Ht); auto.
*
intros ->.
assert (H1 : p_bool (hfs_tuple (vec_map (@proj1_sig _ _) v)) = true).
{
apply p_bool_spec.
apply p_bool_spec in Ht.
apply hfs_trans_opair_inv, proj2, hfs_trans_pair_inv in Ht; tauto.
}
exists (exist _ (hfs_tuple (vec_map (@proj1_sig _ _) v)) H1); split.
-
rewrite is_opair; simpl; auto.
-
Admitted.

Let has_tuples : mb_has_tuples mem yl nt.
Proof.
intros v Hv.
set (t := hfs_tuple (vec_map (proj1_sig (P:=fun x : hfs => p_bool x = true)) v)).
assert (H1 : p_bool t = true).
{
apply p_bool_spec, Hp6; auto; intro; rew vec; apply Hv.
}
exists (exist _ t H1).
Admitted.

Let i' : X -> Y.
Proof.
intros x.
exists (i x).
apply p_bool_spec.
Admitted.

Let Hi'' x : mem (i' x) yl.
Proof.
Admitted.

Theorem reln_hfs : { Y : Type & { _ : finite_t Y & { _ : discrete Y & { mem : Y -> Y -> Prop & { _ : forall u v, { mem u v } + { ~ mem u v } & { yl : Y & { yr : Y & { i : X -> Y & { s : Y -> X & mb_member_ext mem /\ mb_has_tuples mem yl nt /\ (forall x, mem (i x) yl) /\ (forall y, mem y yl -> exists x, y = i x) /\ (forall x, s (i x) = x) /\ (forall v, R v <-> mb_is_tuple_in mem yr (vec_map i v)) /\ (forall x y, mb_equiv mem x y <-> x = y) }}}}}}}}}.
Proof.
exists Y, HY, discrY, mem, mem_dec, yl, yr, i', s'.
msplit 6; auto.
+
intros (u & Hu) (v & Hv) (w & Hw); unfold mem; simpl.
unfold mb_equiv; simpl; intros H.
cut (u = v); [ intros []; auto | ].
apply hfs_mem_ext.
apply p_bool_spec in Hu.
apply p_bool_spec in Hv.
clear w Hw.
intros x; split; intros Hx.
*
generalize (Hp1 Hx Hu); rewrite p_bool_spec; intros H'.
apply (H (exist _ x H')); auto.
*
generalize (Hp1 Hx Hv); rewrite p_bool_spec; intros H'.
apply (H (exist _ x H')); auto.
+
intros y Hy; unfold i'.
destruct (Hi' Hy) as (x & Hx).
exists x; apply eqY; simpl; auto.
+
intros v; rewrite Hr3; split.
*
intros Hv.
red.
assert (H1 : p_bool (hfs_tuple (vec_map i v)) = true).
{
apply p_bool_spec, Hp1 with (1 := Hv); auto.
}
exists (exist _ (hfs_tuple (vec_map i v)) H1); split.
-
apply is_tuple; simpl; rewrite vec_map_map; auto.
-
unfold yr; red; simpl; auto.
*
intros ((t & Ht) & H1 & H2).
rewrite is_tuple in H1.
simpl in H1, H2.
rewrite vec_map_map in H1; subst t.
apply H2.
+
intros x y; rewrite is_equiv; split; auto.
Admitted.

Let yl : Y.
Proof.
exists l; apply p_bool_spec, Hp2.

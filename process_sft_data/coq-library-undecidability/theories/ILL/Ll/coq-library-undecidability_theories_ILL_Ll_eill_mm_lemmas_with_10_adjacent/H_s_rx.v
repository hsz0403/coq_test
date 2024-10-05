Require Import List Permutation Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines.MM Require Import mm_defs mm_utils.
From Undecidability.ILL Require Import ILL EILL ill eill.
Set Implicit Arguments.
Local Infix "~p" := (@Permutation _) (at level 70).
Section Minsky.
Variable (n : nat).
Let q (i : nat) : eill_vars := 2*n+i.
Let rx (p : pos n) := pos2nat p.
Let ry (p : pos n) := n+pos2nat p.
Let H_rx : forall p q, rx p = rx q -> p = q.
Proof.
intros p1 p2; unfold rx; intros.
apply pos2nat_inj; lia.
Local Fixpoint mm_linstr_enc i l := match l with | nil => nil | INC x :: l => LL_INC (rx x) (q (1+i)) (q i) :: mm_linstr_enc (1+i) l | DEC x p :: l => LL_FORK (ry x) (q p) (q i) :: LL_DEC (rx x) (q (1+i)) (q i) :: mm_linstr_enc (1+i) l end.
Local Fact mm_linstr_enc_app i l m : mm_linstr_enc i (l++m) = mm_linstr_enc i l ++ mm_linstr_enc (length l+i) m.
Proof.
revert i; induction l as [ | [ x | x p ] l IHl ]; intros i; simpl; f_equal; auto.
rewrite IHl; do 2 f_equal; lia.
f_equal; rewrite IHl; do 2 f_equal; lia.
Local Fact subcode_mm_linstr_enc i x j l : (i,INC x::nil) <sc (j,l) -> In (LL_INC (rx x) (q (1+i)) (q i)) (mm_linstr_enc j l).
Proof.
intros (l1 & l2 & H1 & H2); subst.
rewrite mm_linstr_enc_app.
apply in_or_app; right; left; do 2 f_equal; lia.
Local Fact subcode_mm_linstr_dec i x p j l : (i,DEC x p::nil) <sc (j,l) -> incl (LL_FORK (ry x) (q p) (q i) :: LL_DEC (rx x) (q (1+i)) (q i) :: nil) (mm_linstr_enc j l).
Proof.
intros (l1 & l2 & H1 & H2); subst.
rewrite mm_linstr_enc_app.
intros A HA; apply in_or_app; right.
destruct HA as [ HA | [ HA | [] ] ]; subst.
left; do 2 f_equal; lia.
right; left; do 2 f_equal; lia.
Local Fact mm_linstr_enc_spec i ll A : In A (mm_linstr_enc i ll) -> (exists j x, (j,INC x::nil) <sc (i,ll) /\ A = LL_INC (rx x) (q (1+j)) (q j)) \/ (exists j x p, (j,DEC x p::nil) <sc (i,ll) /\ ( A = LL_FORK (ry x) (q p) (q j) \/ A = LL_DEC (rx x) (q (1+j)) (q j) ) ).
Proof.
revert i A; induction ll as [ | [ x | x p ] ll IHll ]; intros i A HA.
destruct HA.
destruct HA as [ HA | HA ].
left; exists i, x; split; auto.
apply IHll in HA.
destruct HA as [ (j & x' & H1 & H2) | (j & x' & p & H1 & H2) ].
left; exists j, x'; split; auto.
apply subcode_trans with (1 := H1); subcode_tac; solve list eq.
right; exists j, x', p; split; auto.
apply subcode_trans with (1 := H1); subcode_tac; solve list eq.
destruct HA as [ HA | HA ].
right; exists i, x, p; split; auto.
destruct HA as [ HA | HA ].
right; exists i, x, p; split; auto.
apply IHll in HA.
destruct HA as [ (j & x' & H1 & H2) | (j & x' & p' & H1 & H2) ].
left; exists j, x'; split; auto.
apply subcode_trans with (1 := H1); subcode_tac; solve list eq.
right; exists j, x', p'; split; auto.
apply subcode_trans with (1 := H1); subcode_tac; solve list eq.
Variable (P : nat*(list (mm_instr (pos n)))) (k : nat) (Hk : out_code k P).
Definition Σ0 := LL_INC (q k) (q k) (q k) :: map (fun c => LL_DEC (rx (fst c)) (ry (snd c)) (ry (snd c))) (pos_not_diag n) ++ map (fun j => LL_INC (ry j) (ry j) (ry j)) (pos_list n).
Definition ΣI := match P with (i,l) => mm_linstr_enc i l end.
Definition Σ := Σ0++ΣI.
Notation "P // s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t).
Notation "P // s ->> t" := (sss_compute (@mm_sss _) P s t).
Local Definition s (x : eill_vars) (v : vec nat n) : Prop.
Proof.
refine (match le_lt_dec n x with | left H1 => match le_lt_dec (2*n) x with | left _ => P // (x-2*n,v) ->> (k,vec_zero) | right H2 => vec_pos v (@nat2pos n (x-n) _) = 0 end | right H1 => v = vec_one (@nat2pos n x H1) end); abstract lia.
Defined.
Let H_s_q : forall i v, s (q i) v <-> P // (i,v) ->> (k,vec_zero).
Proof.
intros i v; unfold q, s.
destruct (le_lt_dec n (2*n+i)); [ | lia ].
destruct (le_lt_dec (2*n) (2*n+i)); [ | lia ].
replace (2*n+i-2*n) with i by lia; tauto.
Let H_s_rx : forall p v, s (rx p) v <-> v = vec_one p.
Proof.
intros p v; unfold s, rx.
destruct (le_lt_dec n (pos2nat p)).
generalize (pos2nat_prop p); lia.
rewrite nat2pos_pos2nat; tauto.
Let H_s_ry : forall p v, s (ry p) v <-> vec_pos v p = 0.
Proof.
intros p v; unfold s, ry.
destruct (le_lt_dec n (n+pos2nat p)); [ | lia ].
destruct (le_lt_dec (2*n) (n+pos2nat p)).
generalize (pos2nat_prop p); lia.
match goal with |- vec_pos _ (nat2pos ?H) = _ <-> _ => replace (nat2pos H) with p end.
tauto.
apply pos2nat_inj; rewrite pos2nat_nat2pos; lia.
Opaque s.
Notation "'[[' A ']]'" := (ill_tps s A) (at level 65).
Let sem_x_y_y i j : i <> j -> [[ ⦑ LL_DEC (rx i) (ry j) (ry j)⦒ ]] vec_zero.
Proof.
intros Hij.
simpl; unfold ill_tps_imp.
intros v Hv.
rewrite H_s_rx in Hv.
intros w Hw.
rewrite H_s_ry in Hw.
rewrite H_s_ry.
rewrite (vec_plus_comm v), vec_zero_plus.
unfold vec_plus; rewrite vec_pos_set.
subst; rewrite Hw, vec_one_spec_neq; auto.
Let sem_y_y_y j : [[ ⦑ LL_INC (ry j) (ry j) (ry j)⦒ ]] vec_zero.
Proof.
simpl; unfold ill_tps_imp.
intros x Hx; rew vec.
generalize (Hx vec_zero); rew vec.
intros H; apply H, H_s_ry; rew vec.
Let sem_k v : [[£ (q k)]] v <-> v = vec_zero.
Proof.
simpl; rewrite H_s_q.
split.
2: intros; subst; exists 0; constructor.
intros H.
apply sss_compute_stop in H; auto.
inversion H; auto.
Let sem_k_k_k : [[ ⦑LL_INC (q k) (q k) (q k)⦒ ]] vec_zero.
Proof.
simpl; unfold ill_tps_imp.
intros x Hx; rew vec.
generalize (Hx vec_zero); rew vec.
intros H; apply H, sem_k; auto.
Let Σ0_zero c : In c Σ0 -> [[ ⦑c⦒ ]] vec_zero.
Proof.
unfold Σ0.
intros [ H | H ]; subst.
+
apply sem_k_k_k.
+
apply in_app_or in H.
destruct H as [ H | H ]; apply in_map_iff in H.
*
destruct H as ((i & j) & H1 & H2); subst.
apply sem_x_y_y; simpl.
apply pos_not_diag_spec in H2; auto.
*
destruct H as (y & H1 & _); subst.
apply sem_y_y_y.
Let ΣI_zero c : In c ΣI -> [[ ⦑c⦒ ]] vec_zero.
Proof.
unfold ΣI.
destruct P as (i & lP).
intros H.
apply mm_linstr_enc_spec in H.
destruct H as [ (j & x & H1 & H2) | (j & x & p & H1 & [ H2 | H2 ]) ]; subst c.
+
simpl; unfold ill_tps_imp.
intros v Hv.
rewrite vec_plus_comm, vec_zero_plus.
apply H_s_q.
apply mm_compute_INC with (1 := H1).
specialize (Hv (vec_one x)).
replace (vec_change v x (S (vec_pos v x))) with (vec_plus (vec_one x) v).
apply H_s_q.
*
apply Hv, H_s_rx; trivial.
*
apply vec_pos_ext.
intros p; rewrite vec_pos_plus.
destruct (pos_eq_dec x p).
-
subst; rewrite vec_one_spec_eq, vec_change_eq; auto.
-
rewrite vec_one_spec_neq, vec_change_neq; auto.
+
simpl; unfold ill_tps_imp.
intros v (Hv1 & Hv2).
rewrite vec_plus_comm, vec_zero_plus.
apply H_s_q.
rewrite H_s_ry in Hv1.
apply mm_compute_DEC_0 with (1 := H1); auto.
apply H_s_q; auto.
+
simpl; unfold ill_tps_imp.
intros v Hv w Hw.
rewrite (vec_plus_comm v), vec_zero_plus.
apply H_s_q.
apply H_s_rx in Hv.
rewrite vec_plus_comm.
assert (exists u, vec_pos (vec_plus v w) x = S u) as Hu.
1: {
exists (vec_pos w x).
rewrite vec_pos_plus; subst.
rewrite vec_one_spec_eq; auto.
}
destruct Hu as (u & Hu).
apply mm_compute_DEC_S with (1 := H1) (u := vec_pos w x); auto.
rewrite vec_pos_plus; subst.
rewrite vec_one_spec_eq; auto.
apply H_s_q.
eq goal Hw; f_equal.
apply vec_pos_ext.
intros r.
destruct (pos_eq_dec x r).
*
subst; rewrite vec_change_eq; auto.
*
rewrite vec_change_neq, vec_pos_plus; auto.
subst; rewrite vec_one_spec_neq; auto.
Let prop_5_2_rec (p : pos n) v Ga : vec_pos v p = 0 -> Σ0; Ga ⊦ ry p -> Σ0; vec_map_list v rx ++ Ga ⊦ ry p.
Proof.
revert Ga.
induction v as [ | r | v w Hv Hw ] using (@vec_nat_induction _); intros Ga.
+
intros _.
rewrite vec_map_list_zero.
auto.
+
destruct (pos_eq_dec r p) as [ H | H ]; rew vec; try discriminate.
intros _ H1.
rewrite vec_map_list_one.
apply in_geill_dec with (rx r) (ry p); auto.
right; apply in_or_app; left.
apply in_map_iff.
exists (r,p); simpl; split; auto.
apply pos_not_diag_spec; auto.
apply in_geill_ax.
+
intros H1 H2.
rewrite vec_pos_plus in H1.
apply in_geill_perm with (vec_map_list v rx ++ vec_map_list w rx ++ Ga).
rewrite vec_map_list_plus, app_ass; auto.
apply Hv.
lia.
apply Hw; auto; lia.
End Minsky.

Let H_rx : forall p q, rx p = rx q -> p = q.
Proof.
intros p1 p2; unfold rx; intros.
Admitted.

Let H_s_q : forall i v, s (q i) v <-> P // (i,v) ->> (k,vec_zero).
Proof.
intros i v; unfold q, s.
destruct (le_lt_dec n (2*n+i)); [ | lia ].
destruct (le_lt_dec (2*n) (2*n+i)); [ | lia ].
Admitted.

Let H_s_ry : forall p v, s (ry p) v <-> vec_pos v p = 0.
Proof.
intros p v; unfold s, ry.
destruct (le_lt_dec n (n+pos2nat p)); [ | lia ].
destruct (le_lt_dec (2*n) (n+pos2nat p)).
generalize (pos2nat_prop p); lia.
match goal with |- vec_pos _ (nat2pos ?H) = _ <-> _ => replace (nat2pos H) with p end.
tauto.
Admitted.

Let sem_x_y_y i j : i <> j -> [[ ⦑ LL_DEC (rx i) (ry j) (ry j)⦒ ]] vec_zero.
Proof.
intros Hij.
simpl; unfold ill_tps_imp.
intros v Hv.
rewrite H_s_rx in Hv.
intros w Hw.
rewrite H_s_ry in Hw.
rewrite H_s_ry.
rewrite (vec_plus_comm v), vec_zero_plus.
unfold vec_plus; rewrite vec_pos_set.
Admitted.

Let sem_y_y_y j : [[ ⦑ LL_INC (ry j) (ry j) (ry j)⦒ ]] vec_zero.
Proof.
simpl; unfold ill_tps_imp.
intros x Hx; rew vec.
generalize (Hx vec_zero); rew vec.
Admitted.

Let sem_k v : [[£ (q k)]] v <-> v = vec_zero.
Proof.
simpl; rewrite H_s_q.
split.
2: intros; subst; exists 0; constructor.
intros H.
apply sss_compute_stop in H; auto.
Admitted.

Let sem_k_k_k : [[ ⦑LL_INC (q k) (q k) (q k)⦒ ]] vec_zero.
Proof.
simpl; unfold ill_tps_imp.
intros x Hx; rew vec.
generalize (Hx vec_zero); rew vec.
Admitted.

Let Σ0_zero c : In c Σ0 -> [[ ⦑c⦒ ]] vec_zero.
Proof.
unfold Σ0.
intros [ H | H ]; subst.
+
apply sem_k_k_k.
+
apply in_app_or in H.
destruct H as [ H | H ]; apply in_map_iff in H.
*
destruct H as ((i & j) & H1 & H2); subst.
apply sem_x_y_y; simpl.
apply pos_not_diag_spec in H2; auto.
*
destruct H as (y & H1 & _); subst.
Admitted.

Let ΣI_zero c : In c ΣI -> [[ ⦑c⦒ ]] vec_zero.
Proof.
unfold ΣI.
destruct P as (i & lP).
intros H.
apply mm_linstr_enc_spec in H.
destruct H as [ (j & x & H1 & H2) | (j & x & p & H1 & [ H2 | H2 ]) ]; subst c.
+
simpl; unfold ill_tps_imp.
intros v Hv.
rewrite vec_plus_comm, vec_zero_plus.
apply H_s_q.
apply mm_compute_INC with (1 := H1).
specialize (Hv (vec_one x)).
replace (vec_change v x (S (vec_pos v x))) with (vec_plus (vec_one x) v).
apply H_s_q.
*
apply Hv, H_s_rx; trivial.
*
apply vec_pos_ext.
intros p; rewrite vec_pos_plus.
destruct (pos_eq_dec x p).
-
subst; rewrite vec_one_spec_eq, vec_change_eq; auto.
-
rewrite vec_one_spec_neq, vec_change_neq; auto.
+
simpl; unfold ill_tps_imp.
intros v (Hv1 & Hv2).
rewrite vec_plus_comm, vec_zero_plus.
apply H_s_q.
rewrite H_s_ry in Hv1.
apply mm_compute_DEC_0 with (1 := H1); auto.
apply H_s_q; auto.
+
simpl; unfold ill_tps_imp.
intros v Hv w Hw.
rewrite (vec_plus_comm v), vec_zero_plus.
apply H_s_q.
apply H_s_rx in Hv.
rewrite vec_plus_comm.
assert (exists u, vec_pos (vec_plus v w) x = S u) as Hu.
1: {
exists (vec_pos w x).
rewrite vec_pos_plus; subst.
rewrite vec_one_spec_eq; auto.
}
destruct Hu as (u & Hu).
apply mm_compute_DEC_S with (1 := H1) (u := vec_pos w x); auto.
rewrite vec_pos_plus; subst.
rewrite vec_one_spec_eq; auto.
apply H_s_q.
eq goal Hw; f_equal.
apply vec_pos_ext.
intros r.
destruct (pos_eq_dec x r).
*
subst; rewrite vec_change_eq; auto.
*
rewrite vec_change_neq, vec_pos_plus; auto.
Admitted.

Lemma Σ_zero c : In c Σ -> [[ ⦑c⦒ ]] vec_zero.
Proof.
Admitted.

Corollary ill_tps_Σ_zero : ill_tps_list s (map (fun c => !⦑c⦒) Σ) vec_zero.
Proof.
generalize Σ Σ_zero; intros S.
induction S as [ | A S IHS ]; intros HS.
+
simpl; auto.
+
simpl; exists vec_zero, vec_zero; repeat split; auto.
*
rew vec.
*
apply HS; left; auto.
*
Admitted.

Theorem lemma_5_5 v i : Σ; vec_map_list v rx ⊦ q i -> P // (i,v) ->> (k,vec_zero).
Proof.
intros H.
apply G_eill_S_ill_wc in H.
apply ill_tps_sound with (s := s) in H.
red in H.
specialize (H v).
rewrite vec_plus_comm, vec_zero_plus in H.
apply H_s_q; auto.
apply H.
rewrite ill_tps_app.
exists vec_zero, v; repeat split.
+
rew vec.
+
apply ill_tps_Σ_zero.
+
Admitted.

Let H_s_rx : forall p v, s (rx p) v <-> v = vec_one p.
Proof.
intros p v; unfold s, rx.
destruct (le_lt_dec n (pos2nat p)).
generalize (pos2nat_prop p); lia.
rewrite nat2pos_pos2nat; tauto.

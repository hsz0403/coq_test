Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.DecompositionWithPostState.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineCorrectInterface.
Section StateMachineCorrect.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {si : sorted_interface}.
Context {misi : max_index_sanity_interface}.
Context {smsi : state_machine_safety_interface}.
Context {lmi : log_matching_interface}.
Ltac get_invariant_pre inv := match goal with | H : raft_intermediate_reachable _ |- _=> match (type of H) with | context [mkNetwork] => fail 2 end || copy_apply inv H end.
Ltac get_invariant_post inv := match goal with | H : raft_intermediate_reachable _ |- _=> match (type of H) with | context [mkNetwork] => copy_apply inv H end end.
Definition clientCache_to_ks (c : list (clientId * (nat * output))) := map (fun e => (fst e, fst (snd e))) c.
Fixpoint log_to_ks' (l : list entry) (ks : list (clientId * nat)) : list (clientId * nat) := match l with | e :: l' => if (assoc_default clientId_eq_dec ks (eClient e) 0) <=? eId e then log_to_ks' l' (assoc_set clientId_eq_dec ks (eClient e) (eId e)) else log_to_ks' l' ks | [] => ks end.
Definition log_to_ks l := log_to_ks' l [].
Definition client_cache_keys_correct net := forall h, a_equiv clientId_eq_dec (clientCache_to_ks (clientCache (nwState net h))) (log_to_ks' (rev (removeAfterIndex (log (nwState net h)) (lastApplied (nwState net h)))) []).
Fixpoint max_id_for_client_default (default : nat) (c : clientId) (l : list entry) : nat := match l with | [] => default | e :: l' => if clientId_eq_dec c (eClient e) then max_id_for_client_default (max default (eId e)) c l' else max_id_for_client_default default c l' end.
Ltac use_same_client_cache hyp := erewrite same_clientCache_same_getLastId in *; [|eapply hyp]; eauto.
Instance smci : state_machine_correct_interface.
Proof.
split.
exact state_machine_correct_invariant.
End StateMachineCorrect.

Lemma filter_false : forall A (l : list A), filter (fun _ => false) l = [].
Proof using.
intros.
Admitted.

Lemma filter_and : forall A (l : list A) f g, (forall x, In x l -> f x = true) -> filter (fun x => f x && g x) l = filter (fun x => g x) l.
Proof using.
intros.
induction l; simpl in *; auto.
repeat break_if; do_bool; simpl in *; auto.
-
f_equal; eauto.
-
intuition.
congruence.
-
intuition; try congruence.
assert (f a = true) by eauto.
Admitted.

Lemma removeAfterIndex_app : forall l i i', sorted l -> i' < i -> removeAfterIndex l i = filter (fun x => eIndex x <=? i) (findGtIndex l i') ++ removeAfterIndex l i'.
Proof using.
intros.
induction l; simpl in *; auto.
repeat (break_match; simpl in *); do_bool; intuition; try omega; try congruence.
f_equal.
repeat find_reverse_rewrite.
rewrite removeAfterIndex_eq; auto.
intros.
find_apply_hyp_hyp.
Admitted.

Lemma log_to_ks'_app : forall l1 l2 ks, log_to_ks' (l1 ++ l2) ks = log_to_ks' l2 (log_to_ks' l1 ks).
Proof using.
induction l1; intros; simpl in *; auto.
Admitted.

Lemma log_to_ks'_a_equiv : forall l ks ks', a_equiv clientId_eq_dec ks ks' -> a_equiv clientId_eq_dec (log_to_ks' l ks) (log_to_ks' l ks').
Proof using.
induction l; intros; simpl.
-
auto.
-
erewrite assoc_default_a_equiv by eauto.
Admitted.

Lemma log_to_ks'_max_id_for_client : forall l c ks, assoc_default clientId_eq_dec (log_to_ks' l ks) c 0 = max_id_for_client_default (assoc_default clientId_eq_dec ks c 0) c l.
Proof using.
induction l; simpl; intros.
-
auto.
-
repeat break_match; do_bool; rewrite IHl; subst; auto.
+
rewrite get_set_same_default.
now rewrite max_r by auto.
+
now rewrite get_set_diff_default by auto.
+
Admitted.

Lemma max_id_for_client_default_le : forall l x c, (forall e, In e l -> eClient e = c -> eId e <= x) -> max_id_for_client_default x c l = x.
Proof using.
induction l; simpl; intros.
-
auto.
-
break_if.
+
rewrite IHl.
*
subst.
now rewrite max_l by eauto.
*
intros.
subst.
eapply le_trans; [| apply Max.le_max_l].
eauto.
+
Admitted.

Lemma max_id_for_client_default_on_max : forall c l x x', max_id_for_client_default (max x x') c l = max x (max_id_for_client_default x' c l).
Proof using.
induction l; simpl; intros.
-
auto.
-
break_if; repeat rewrite IHl.
2: reflexivity.
zify.
Admitted.

Lemma max_id_for_client_default_or_entry : forall c l x, max_id_for_client_default x c l = x \/ exists e, In e l /\ eClient e = c /\ max_id_for_client_default x c l = eId e.
Proof using.
induction l; simpl; intuition.
break_if.
-
specialize (IHl (max x (eId a))).
intuition.
+
destruct (le_lt_dec x (eId a)).
*
rewrite max_r in * by auto.
right.
eauto.
*
rewrite max_l in * by omega.
auto.
+
right.
break_exists.
break_and.
rewrite max_id_for_client_default_on_max in *.
exists x0.
intuition.
-
specialize (IHl x).
intuition.
right.
break_exists_exists.
Admitted.

Lemma max_id_for_client_default_is_max : forall l x c e, In e l -> eClient e = c -> eId e <= max_id_for_client_default x c l.
Proof using.
induction l; simpl; intuition; subst.
-
break_if; try congruence.
rewrite Max.max_comm.
rewrite max_id_for_client_default_on_max.
apply Max.le_max_l.
-
Admitted.

Lemma max_id_for_client_default_subset : forall l l' x c, (forall e, In e l -> In e l') -> max_id_for_client_default x c l <= max_id_for_client_default x c l'.
Proof using.
intros.
pose proof max_id_for_client_default_or_entry c l x.
pose proof max_id_for_client_default_or_entry c l' x.
intuition; break_exists; intuition; repeat find_rewrite.
-
eapply le_trans; [|eapply Nat.eq_le_incl].
apply max_id_for_client_default_ge_default.
eauto.
-
find_apply_hyp_hyp.
eapply le_trans.
+
apply max_id_for_client_default_is_max; eauto.
+
eauto using Nat.eq_le_incl.
-
find_apply_hyp_hyp.
eapply le_trans.
+
apply max_id_for_client_default_is_max; eauto.
+
Admitted.

Lemma max_id_for_client_default_ext : forall l l' x c, (forall e, In e l -> In e l') -> (forall e, In e l' -> In e l) -> max_id_for_client_default x c l = max_id_for_client_default x c l'.
Proof using.
intros.
Admitted.

Lemma log_to_ks'_assoc_default_ks : forall l ks c i, i <= assoc_default clientId_eq_dec (log_to_ks' l (assoc_set clientId_eq_dec ks c i)) c 0.
Proof using.
induction l; intros; simpl.
-
rewrite assoc_default_assoc_set.
auto.
-
break_if; simpl in *; eauto.
do_bool.
destruct (clientId_eq_dec (eClient a) c); simpl in *; auto.
+
subst.
find_rewrite_lem assoc_default_assoc_set.
rewrite assoc_set_assoc_set_same.
eauto using le_trans.
+
erewrite assoc_default_a_equiv; [|eapply log_to_ks'_a_equiv; eapply assoc_set_assoc_set_diff; auto].
Admitted.

Lemma log_to_ks'_assoc_default_assoc_default_le : forall l ks c, assoc_default clientId_eq_dec ks c 0 <= assoc_default clientId_eq_dec (log_to_ks' l ks) c 0.
Proof using.
induction l; intros; simpl in *; auto.
break_if; simpl in *; eauto.
do_bool.
destruct (clientId_eq_dec (eClient a) c); simpl in *; subst; auto.
-
eapply le_trans; eauto.
eauto using log_to_ks'_assoc_default_ks.
-
match goal with | [ |- context [ assoc_set ?e ?ks ?c' ?i ] ] => assert (assoc_default e ks c 0 = assoc_default e (assoc_set e ks c' i) c 0) end; repeat find_rewrite; eauto.
Admitted.

Lemma log_to_ks'_assoc_default_eq : forall l ks ks' c, assoc_default clientId_eq_dec (log_to_ks' l ks) c 0 <= assoc_default clientId_eq_dec ks' c 0 -> assoc_default clientId_eq_dec (log_to_ks' l ks') c 0 = assoc_default clientId_eq_dec ks' c 0.
Proof using.
induction l; intros; simpl in *; auto.
repeat break_if; do_bool; simpl in *; eauto.
-
destruct (clientId_eq_dec (eClient a) c); simpl in *; auto.
+
subst.
match goal with | [ |- context [ assoc_set ?e ?ks ?c ?i ] ] => assert (assoc_default e ks c 0 = assoc_default e (assoc_set e ks c i) c 0) end; repeat find_rewrite; eauto.
rewrite assoc_default_assoc_set.
eapply le_antisym; eauto.
eapply le_trans; [|eauto]; eauto using log_to_ks'_assoc_default_ks.
+
match goal with | [ |- context [ assoc_set ?e ?ks ?c' ?i ] ] => assert (assoc_default e ks c 0 = assoc_default e (assoc_set e ks c' i) c 0) end; repeat find_rewrite; eauto.
rewrite assoc_default_assoc_set_diff; auto.
-
destruct (clientId_eq_dec (eClient a) c); simpl in *; auto.
+
subst.
match goal with | [ |- context [ assoc_set ?e ?ks ?c ?i ] ] => assert (assoc_default e ks c 0 = assoc_default e (assoc_set e ks c i) c 0) end; repeat find_rewrite; eauto.
rewrite assoc_default_assoc_set.
eapply le_antisym; eauto.
eapply le_trans; [|eauto]; eauto using log_to_ks'_assoc_default_ks.
eapply le_trans; [|eauto using log_to_ks'_assoc_default_assoc_default_le].
omega.
+
match goal with | [ |- context [ assoc_set ?e ?ks ?c' ?i ] ] => assert (assoc_default e ks c 0 = assoc_default e (assoc_set e ks c' i) c 0) end; repeat find_rewrite; eauto.
Admitted.

Lemma log_to_ks'_assoc_set_diff : forall l ks k v k', k <> k' -> assoc clientId_eq_dec (log_to_ks' l (assoc_set clientId_eq_dec ks k v)) k' = assoc clientId_eq_dec (log_to_ks' l ks) k'.
Proof using.
induction l; intros; simpl in *.
-
rewrite get_set_diff by auto.
auto.
-
repeat break_match; simpl in *; eauto.
+
do_bool.
destruct (clientId_eq_dec (eClient a) k); subst; simpl in *.
*
rewrite assoc_set_assoc_set_same.
auto.
*
erewrite assoc_a_equiv; [|apply log_to_ks'_a_equiv; apply assoc_set_assoc_set_diff]; eauto.
+
do_bool.
destruct (clientId_eq_dec (eClient a) k); subst; simpl in *.
*
rewrite assoc_set_assoc_set_same.
auto.
*
rewrite assoc_default_assoc_set_diff in *; auto; omega.
+
do_bool.
destruct (clientId_eq_dec (eClient a) k); subst; simpl in *.
*
erewrite <- assoc_set_assoc_set_same; eauto.
*
Admitted.

Lemma log_to_ks'_assoc_default_set_diff : forall l ks k v k', k <> k' -> assoc_default clientId_eq_dec (log_to_ks' l (assoc_set clientId_eq_dec ks k v)) k' 0 = assoc_default clientId_eq_dec (log_to_ks' l ks) k' 0.
Proof using.
induction l; intros; simpl in *; auto using assoc_default_assoc_set_diff.
repeat break_match; simpl in *; eauto.
-
do_bool.
destruct (clientId_eq_dec (eClient a) k); subst; simpl in *.
+
rewrite assoc_set_assoc_set_same.
auto.
+
erewrite assoc_default_a_equiv; [|apply log_to_ks'_a_equiv; apply assoc_set_assoc_set_diff]; eauto.
-
do_bool.
destruct (clientId_eq_dec (eClient a) k); subst; simpl in *.
+
rewrite assoc_set_assoc_set_same.
auto.
+
rewrite assoc_default_assoc_set_diff in *; auto; omega.
-
do_bool.
destruct (clientId_eq_dec (eClient a) k); subst; simpl in *.
+
erewrite <- assoc_set_assoc_set_same; eauto.
+
Admitted.

Lemma assoc_set_log_to_ks'_le: forall (l : list entry) (ks : list (clientId * nat)) c i, assoc_default clientId_eq_dec (log_to_ks' l ks) c 0 <= i -> a_equiv clientId_eq_dec (assoc_set clientId_eq_dec (log_to_ks' l ks) c i) (log_to_ks' l (assoc_set clientId_eq_dec ks c i)).
Proof using.
induction l; intros; simpl in *; eauto using a_equiv_refl.
repeat break_if; simpl in *; eauto.
-
do_bool.
destruct (clientId_eq_dec (eClient a) c); subst.
+
repeat rewrite assoc_set_assoc_set_same.
find_rewrite_lem assoc_default_assoc_set.
assert (i = eId a) by (eapply le_antisym; auto; eapply le_trans; [|eauto]; eauto using log_to_ks'_assoc_default_ks).
subst.
find_apply_hyp_hyp.
find_rewrite_lem assoc_set_assoc_set_same.
auto.
+
eapply a_equiv_sym.
eapply a_equiv_trans; [eapply log_to_ks'_a_equiv; eapply assoc_set_assoc_set_diff; auto|].
eapply a_equiv_sym.
eauto.
-
do_bool.
destruct (clientId_eq_dec (eClient a) c); subst.
+
find_rewrite_lem assoc_default_assoc_set.
find_apply_hyp_hyp.
find_rewrite_lem assoc_set_assoc_set_same.
auto.
+
rewrite assoc_default_assoc_set_diff in *; auto.
omega.
-
do_bool.
destruct (clientId_eq_dec (eClient a) c); subst.
+
find_rewrite_lem assoc_default_assoc_set.
rewrite assoc_set_assoc_set_same.
assert (i = eId a); subst; eauto.
eapply le_antisym; eauto.
eapply le_trans; [|eauto].
eapply le_trans; [|eapply log_to_ks'_assoc_default_assoc_default_le].
omega.
+
rewrite assoc_default_assoc_set_diff in *; auto.
Admitted.

Lemma in_ks_log_to_ks'_le : forall e l ks id, assoc clientId_eq_dec ks (eClient e) = Some id -> exists id', assoc clientId_eq_dec (log_to_ks' l ks) (eClient e) = Some id' /\ id <= id'.
Proof using.
induction l; simpl; intuition.
-
eauto.
-
break_if; do_bool.
+
destruct (clientId_eq_dec (eClient e) (eClient a)).
*
repeat find_rewrite.
unfold assoc_default in *.
find_rewrite.
specialize (IHl (assoc_set clientId_eq_dec ks (eClient a) (eId a)) (eId a)).
conclude_using ltac:(now rewrite get_set_same).
break_exists_exists.
intuition.
*
rewrite log_to_ks'_assoc_set_diff by auto.
auto.
+
Admitted.

Lemma in_l_log_to_ks'_le : forall e l ks, In e l -> exists id, assoc clientId_eq_dec (log_to_ks' l ks) (eClient e) = Some id /\ eId e <= id.
Proof using.
induction l; simpl; intuition.
-
subst.
break_if; do_bool.
+
apply in_ks_log_to_ks'_le.
rewrite get_set_same.
auto.
+
unfold assoc_default in *.
break_match; try omega.
find_eapply_lem_hyp in_ks_log_to_ks'_le.
break_exists_exists.
intuition eauto.
omega.
-
Admitted.

Lemma max_id_for_client_default_ge_default : forall l x c, x <= max_id_for_client_default x c l.
Proof using.
induction l; simpl; intuition.
break_if; intuition.
rewrite max_id_for_client_default_on_max.
apply Max.le_max_l.

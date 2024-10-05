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

Lemma clientCache_to_ks_assoc_none : forall c client, assoc clientId_eq_dec (clientCache_to_ks c) client = None -> assoc clientId_eq_dec c client = None.
Proof using.
induction c; intros; simpl in *; try congruence.
break_if; eauto; try congruence.
-
break_let; subst; simpl in *.
break_if; try congruence.
Admitted.

Lemma clientCache_to_ks_assoc_getLastId_none : forall st client, assoc clientId_eq_dec (clientCache_to_ks (clientCache st)) client = None -> getLastId st client = None.
Proof using.
Admitted.

Lemma cacheApplyEntry_stateMachine_apply : forall st e os st' id o o' d, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = Some (id, o) -> id < eId e -> handler (eInput e) (stateMachine st) = (o', d) -> stateMachine st' = d.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma cacheApplyEntry_cache_apply : forall st e os st' id o o' d, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = Some (id, o) -> id < eId e -> handler (eInput e) (stateMachine st) = (o', d) -> assoc_set clientId_eq_dec (clientCache st) (eClient e) (eId e, o') = clientCache st'.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma cacheApplyEntry_stateMachine_apply_none : forall st e os st' o' d, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = None -> handler (eInput e) (stateMachine st) = (o', d) -> stateMachine st' = d.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma cacheApplyEntry_cache_apply_none : forall st e os st' o' d, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = None -> handler (eInput e) (stateMachine st) = (o', d) -> assoc_set clientId_eq_dec (clientCache st) (eClient e) (eId e, o') = clientCache st'.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma cacheApplyEntry_stateMachine_no_apply : forall st e os st' id o, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = Some (id, o) -> eId e <= id -> stateMachine st' = stateMachine st.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma cacheApplyEntry_cache_no_apply : forall st e os st' id o, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = Some (id, o) -> eId e <= id -> clientCache st = clientCache st'.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma clientCache_to_ks_assoc_set : forall c client id o, assoc_set clientId_eq_dec (clientCache_to_ks c) client id = clientCache_to_ks (assoc_set clientId_eq_dec c client (id, o)).
Proof using.
induction c; intros; simpl in *; intuition.
simpl.
break_if; simpl in *; eauto.
f_equal.
Admitted.

Lemma applyEntries_execute_log' : forall l h st os st', applyEntries h st l = (os, st') -> stateMachine st' = (snd (execute_log' (deduplicate_log' l (clientCache_to_ks (clientCache st))) (stateMachine st) [])).
Proof using.
induction l; intros; simpl in *; intuition.
-
find_inversion.
auto.
-
repeat break_let.
find_inversion.
repeat break_match; simpl in *.
+
break_let.
rewrite snd_execute_log'_nil.
find_apply_hyp_hyp.
do_bool.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_apply; [|eauto|idtac|]; eauto.
subst.
find_eapply_lem_hyp cacheApplyEntry_cache_apply; eauto.
erewrite clientCache_to_ks_assoc_set.
rewrite Heqp1.
eauto.
+
do_bool.
find_apply_hyp_hyp.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
break_exists.
find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_no_apply; eauto.
find_eapply_lem_hyp cacheApplyEntry_cache_no_apply; eauto.
repeat find_rewrite.
auto.
+
break_let.
rewrite snd_execute_log'_nil.
find_apply_hyp_hyp.
do_bool.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId_none.
break_exists.
find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_apply_none; eauto.
subst.
find_eapply_lem_hyp cacheApplyEntry_cache_apply_none; eauto.
erewrite clientCache_to_ks_assoc_set.
rewrite Heqp1.
Admitted.

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

Lemma applyEntries_lastApplied_commitIndex_log : forall l h st os st', applyEntries h st l = (os, st') -> lastApplied st' = lastApplied st /\ commitIndex st' = commitIndex st /\ log st' = log st.
Proof using.
induction l; simpl in *; intros.
-
find_inversion.
auto.
-
repeat break_match; find_inversion; simpl in *; unfold cacheApplyEntry, applyEntry in *; repeat break_match; find_inversion; simpl in *; eauto; copy_eapply_prop_hyp applyEntries applyEntries; intuition; simpl in *; auto.

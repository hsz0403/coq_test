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

Lemma applyEntries_lastApplied_commitIndex_log : forall l h st os st', applyEntries h st l = (os, st') -> lastApplied st' = lastApplied st /\ commitIndex st' = commitIndex st /\ log st' = log st.
Proof using.
induction l; simpl in *; intros.
-
find_inversion.
auto.
-
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

Lemma max_id_for_client_default_ge_default : forall l x c, x <= max_id_for_client_default x c l.
Proof using.
induction l; simpl; intuition.
break_if; intuition.
rewrite max_id_for_client_default_on_max.
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

Lemma handleAppendEntries_preserves_lastApplied_entries': forall (p : packet) (net : network) (d : raft_data) (m : msg) (t : term) (n : name) (pli : logIndex) (plt : term) (es : list entry) (ci : logIndex) xs ys ps' st' e, raft_intermediate_reachable net -> raft_intermediate_reachable {| nwPackets := ps'; nwState := st' |} -> (forall h : name, st' h = update name_eq_dec (nwState net) (pDst p) d h) -> (forall p' : packet, In p' ps' -> In p' (xs ++ ys) \/ p' = {| pSrc := pDst p; pDst := pSrc p; pBody := m |}) -> handleAppendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci = (d, m) -> nwPackets net = xs ++ p :: ys -> pBody p = AppendEntries t n pli plt es ci -> eIndex e <= lastApplied (nwState net (pDst p)) -> In e (log (nwState net (pDst p))) -> In e (log d).
Proof using lmi smsi misi.
intros.
get_invariant_post max_index_sanity_invariant.
unfold maxIndex_sanity in *; intuition.
unfold maxIndex_lastApplied in *; intuition.
match goal with | H : forall _, lastApplied _ <= maxIndex _ |- _ => specialize (H (pDst p)) end.
simpl in *.
repeat find_higher_order_rewrite.
rewrite_update.
repeat find_rewrite.
get_invariant_pre state_machine_safety_invariant.
unfold state_machine_safety in *.
intuition.
match goal with | H : state_machine_safety_nw _ |- _ => specialize (H (pDst p)) end.
find_copy_apply_lem_hyp handleAppendEntries_log.
intuition; repeat find_rewrite; eauto.
-
match goal with | _ : eIndex ?e <= lastApplied (nwState ?net ?h) |- _ => assert (commit_recorded net h e) by (unfold commit_recorded; eauto) end.
get_invariant_pre log_matching_invariant.
unfold log_matching, log_matching_hosts in *.
intuition.
copy_eapply_prop_hyp In In.
copy_eapply_prop_hyp pBody pBody; eauto.
intuition; try omega.
subst.
find_copy_apply_lem_hyp handleAppendEntries_same_lastApplied.
repeat find_rewrite.
omega.
-
match goal with | _ : eIndex ?e <= lastApplied (nwState ?net ?h) |- _ => assert (commit_recorded net h e) by (unfold commit_recorded; eauto) end.
get_invariant_pre log_matching_invariant.
unfold log_matching, log_matching_hosts in *.
intuition.
copy_eapply_prop_hyp In In.
copy_eapply_prop_hyp pBody pBody; eauto.
intuition.
+
apply in_app_iff.
right.
apply removeAfterIndex_le_In; eauto; omega.
+
apply in_app_iff.
right.
apply removeAfterIndex_le_In; eauto; omega.
+
match goal with | _ : context [maxIndex (?a ++ ?b)] |- _ => pose proof maxIndex_app a b end.
intuition.
repeat find_rewrite.
find_copy_apply_lem_hyp handleAppendEntries_same_lastApplied.
repeat find_rewrite.
Admitted.

Lemma handleAppendEntries_preserves_lastApplied_entries: forall (p : packet) (net : network) (d : raft_data) (m : msg) (t : term) (n : name) (pli : logIndex) (plt : term) (es : list entry) (ci : logIndex) xs ys ps' st', raft_intermediate_reachable net -> raft_intermediate_reachable {| nwPackets := ps'; nwState := st' |} -> (forall h : name, st' h = update name_eq_dec (nwState net) (pDst p) d h) -> (forall p' : packet, In p' ps' -> In p' (xs ++ ys) \/ p' = {| pSrc := pDst p; pDst := pSrc p; pBody := m |}) -> handleAppendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci = (d, m) -> nwPackets net = xs ++ p :: ys -> pBody p = AppendEntries t n pli plt es ci -> removeAfterIndex (log d) (lastApplied d) = removeAfterIndex (log (nwState net (pDst p))) (lastApplied (nwState net (pDst p))).
Proof using lmi smsi misi si.
intros.
find_copy_apply_lem_hyp handleAppendEntries_same_lastApplied.
repeat find_rewrite.
get_invariant_pre logs_sorted_invariant.
get_invariant_post logs_sorted_invariant.
unfold logs_sorted in *.
intuition.
apply removeAfterIndex_same_sufficient; auto.
-
unfold logs_sorted_host in *.
simpl in *.
match goal with | H : forall h, sorted (log (st' h)) |- _ => specialize (H (pDst p)) end.
repeat find_higher_order_rewrite.
rewrite_update.
auto.
-
intros.
eauto using handleAppendEntries_preserves_lastApplied_entries'.
-
intros.
get_invariant_pre max_index_sanity_invariant.
unfold maxIndex_sanity, maxIndex_lastApplied in *.
intuition.
enough (exists e', eIndex e' = eIndex e /\ In e' (log (nwState net (pDst p)))).
+
break_exists.
intuition.
find_copy_eapply_lem_hyp handleAppendEntries_preserves_lastApplied_entries'; repeat find_rewrite; eauto.
enough (x = e) by now subst.
eapply uniqueIndices_elim_eq; eauto.
apply sorted_uniqueIndices.
unfold logs_sorted_host in *.
simpl in *.
match goal with | H : forall h, sorted (log (st' h)) |- _ => specialize (H (pDst p)) end.
repeat find_higher_order_rewrite.
rewrite_update.
auto.
+
apply log_matching_invariant; auto.
intuition; eauto using le_trans.
enough (eIndex e > 0) by auto.
get_invariant_post log_matching_invariant.
unfold log_matching, log_matching_hosts in *.
intuition.
match goal with | H : context [eIndex _ > _] |- _ => eapply H with (h := (pDst p)) end.
simpl.
repeat find_higher_order_rewrite.
rewrite_update.
Admitted.

Lemma removeAfterIndex_cons : forall l x i, i < eIndex x -> removeAfterIndex (x :: l) i = removeAfterIndex l i.
Proof using.
intros.
Admitted.

Lemma handleClientRequest_preserves_lastApplied_entries: forall h (net : network) (d : raft_data) client id c out l, raft_intermediate_reachable net -> handleClientRequest h (nwState net h) client id c = (out, d, l) -> removeAfterIndex (log d) (lastApplied d) = removeAfterIndex (log (nwState net h)) (lastApplied (nwState net h)).
Proof using misi.
intros.
erewrite handleClientRequest_lastApplied; eauto.
find_apply_lem_hyp handleClientRequest_log.
intuition; repeat find_rewrite; eauto.
break_exists; intuition; repeat find_rewrite.
erewrite removeAfterIndex_cons; eauto.
get_invariant_pre max_index_sanity_invariant.
unfold maxIndex_sanity, maxIndex_lastApplied in *.
intuition.
match goal with | H : forall _, lastApplied _ <= maxIndex _ |- _ => specialize (H h) end.
Admitted.

Lemma client_cache_keys_correct_clientCache_complete : forall net, client_cache_keys_correct net -> client_cache_complete net.
Proof using.
unfold client_cache_keys_correct, client_cache_complete.
intros.
unfold getLastId.
enough (exists id, assoc clientId_eq_dec (clientCache_to_ks (clientCache (nwState net h))) (eClient e) = Some id /\ eId e <= id).
-
break_exists_exists.
intuition.
find_apply_lem_hyp clientCache_to_ks_assoc.
break_exists_exists.
intuition.
-
erewrite assoc_a_equiv by eauto.
find_apply_lem_hyp in_rev.
Admitted.

Lemma deduplicate_log'_app : forall l1 l2 ks, deduplicate_log' (l1 ++ l2) ks = deduplicate_log' l1 ks ++ (deduplicate_log' l2 (log_to_ks' l1 ks)).
Proof using.
induction l1; intros; simpl in *; auto.
repeat break_match; simpl in *; eauto; try solve [f_equal; eauto].
-
exfalso.
do_bool.
find_erewrite_lem assoc_assoc_default.
omega.
-
do_bool.
find_erewrite_lem assoc_assoc_default.
rewrite assoc_set_same; eauto.
find_eapply_lem_hyp le_antisym; eauto.
subst.
auto.
-
exfalso.
do_bool.
find_erewrite_lem assoc_assoc_default_missing.
Admitted.

Lemma deduplicate_log'_a_equiv : forall l ks ks', a_equiv clientId_eq_dec ks ks' -> deduplicate_log' l ks = deduplicate_log' l ks'.
Proof using.
induction l; intros; simpl in *; auto.
Admitted.

Lemma cacheApplyEntry_getLastId : forall st e l st' client id out, cacheApplyEntry st e = (l, st') -> getLastId st' client = Some (id, out) -> getLastId st client = Some (id, out) \/ eClient e = client /\ l = [out] /\ eId e = id /\ out = fst (handler (eInput e) (stateMachine st)) /\ (forall id' out', getLastId st client = Some (id', out') -> id' < id).
Proof using.
intros.
unfold cacheApplyEntry in *.
repeat break_match; try find_inversion; subst; auto; do_bool.
-
unfold applyEntry in *.
break_let.
find_inversion.
simpl in *.
match goal with | H : context [assoc_set] |- _ => unfold getLastId in H; simpl in H end.
destruct (clientId_eq_dec client (eClient e)); try now rewrite get_set_diff in *; auto.
subst.
rewrite get_set_same in *.
find_inversion.
repeat find_rewrite.
right.
intuition.
find_inversion.
omega.
-
unfold applyEntry in *.
break_let.
find_inversion.
simpl in *.
match goal with | H : context [assoc_set] |- _ => unfold getLastId in H; simpl in H end.
destruct (clientId_eq_dec client (eClient e)); try now rewrite get_set_diff in *; auto.
subst.
rewrite get_set_same in *.
find_inversion.
repeat find_rewrite.
right.
intuition.
Admitted.

Lemma applyEntries_app : forall l h st os d l', applyEntries h st (l ++ l') = (os, d) -> exists os' os'' d', applyEntries h st l = (os', d') /\ applyEntries h d' l' = (os'', d) /\ os = os' ++ os''.
Proof using.
induction l; intros; simpl in *; try now repeat eexists; eauto.
repeat break_let.
find_inversion.
find_apply_hyp_hyp.
break_exists.
intuition.
repeat find_rewrite.
find_inversion.
Admitted.

Lemma getLastId_clientCache_to_ks_assoc : forall (st : RaftState.raft_data term name entry logIndex serverType data clientId output) (client : clientId) (id : nat) o, getLastId st client = Some (id, o) -> assoc clientId_eq_dec (clientCache_to_ks (clientCache st)) client = Some id.
Proof using.
intros.
unfold getLastId in *.
induction (clientCache st).
-
simpl in *.
congruence.
-
simpl in *.
break_let.
subst.
simpl in *.
Admitted.

Lemma i_lt_assoc_default_0 : forall K K_eq_dec ks (k : K) i, i < assoc_default K_eq_dec ks k 0 -> exists i', assoc K_eq_dec ks k = Some i' /\ i < i'.
Proof using.
intros.
unfold assoc_default in *.
Admitted.

Lemma applyEntries_log_to_ks' : forall l h st o st', applyEntries h st l = (o, st') -> a_equiv clientId_eq_dec (clientCache_to_ks (clientCache st')) (log_to_ks' l (clientCache_to_ks (clientCache st))).
Proof using.
induction l; intros; simpl in *; intuition.
-
find_inversion.
apply a_equiv_refl.
-
repeat break_let.
find_inversion.
break_if.
+
do_bool.
unfold cacheApplyEntry in *.
repeat break_match; repeat find_inversion; do_bool.
*
find_apply_lem_hyp getLastId_clientCache_to_ks_assoc.
find_erewrite_lem assoc_assoc_default.
omega.
*
find_apply_hyp_hyp.
subst.
rewrite assoc_set_same; eauto using a_equiv_refl.
eauto using getLastId_clientCache_to_ks_assoc.
*
subst.
unfold applyEntry in *.
break_let.
find_inversion.
find_apply_hyp_hyp.
eapply a_equiv_trans; eauto.
simpl.
erewrite clientCache_to_ks_assoc_set; eauto using a_equiv_refl.
*
subst.
unfold applyEntry in *.
break_let.
find_inversion.
find_apply_hyp_hyp.
eapply a_equiv_trans; eauto.
simpl.
erewrite clientCache_to_ks_assoc_set; eauto using a_equiv_refl.
+
do_bool.
find_apply_lem_hyp i_lt_assoc_default_0.
break_exists.
intuition.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
unfold cacheApplyEntry in *.
repeat find_rewrite.
break_if; do_bool; try omega.
find_inversion.
Admitted.

Lemma applyEntries_execute_log'_cache : forall l h st os st' client id out, applyEntries h st l = (os, st') -> getLastId st' client = Some (id, out) -> (getLastId st client = Some (id, out) \/ exists e xs ys, deduplicate_log' l (clientCache_to_ks (clientCache st)) = xs ++ e :: ys /\ eClient e = client /\ eId e = id /\ Some (eInput e, out) = hd_error (rev (fst (execute_log' (xs ++ [e]) (stateMachine st) [])))).
Proof using.
induction l using rev_ind; intros; simpl in *; intuition; repeat break_let; repeat find_inversion; auto.
find_apply_lem_hyp applyEntries_app.
break_exists.
intuition.
simpl in *.
break_let.
find_inversion.
unfold cacheApplyEntry in *.
repeat break_match.
-
subst.
find_inversion.
copy_eapply_prop_hyp applyEntries applyEntries; [| match goal with | H : context [id] |- _ => apply H end].
intuition.
right.
break_exists_name e; exists e.
break_exists_name xs.
exists xs.
break_exists_name ys.
break_exists.
intuition.
subst.
match goal with | _ : deduplicate_log' ?l ?ks = _ |- _ => pose proof deduplicate_log'_app l [x] ks end.
repeat find_rewrite.
repeat eexists; eauto.
rewrite app_ass.
rewrite <- app_comm_cons.
eauto.
-
do_bool.
repeat find_inversion.
copy_eapply_prop_hyp applyEntries applyEntries; [| match goal with | H : context [id] |- _ => apply H end].
intuition.
right.
break_exists_name e; exists e.
break_exists_name xs.
exists xs.
break_exists_name ys.
break_exists.
intuition.
subst.
match goal with | _ : deduplicate_log' ?l ?ks = _ |- _ => pose proof deduplicate_log'_app l [x] ks end.
repeat find_rewrite.
repeat eexists; eauto.
rewrite app_ass.
rewrite <- app_comm_cons.
eauto.
-
do_bool.
subst.
destruct (clientId_eq_dec (eClient x) client).
+
subst.
assert (id = eId x).
{
unfold applyEntry in *.
break_let.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_same in *.
find_inversion.
auto.
}
subst.
right.
unfold applyEntry in *.
break_let.
find_inversion.
exists x, (deduplicate_log' l (clientCache_to_ks (clientCache st))), [].
intuition.
*
rewrite deduplicate_log'_app.
f_equal.
simpl in *.
repeat break_match; auto.
do_bool.
find_apply_lem_hyp applyEntries_log_to_ks'.
find_apply_lem_hyp a_equiv_sym.
find_erewrite_lem assoc_a_equiv; eauto.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
repeat find_rewrite.
find_inversion.
omega.
*
rewrite execute_log'_app.
break_let.
simpl in *.
break_let.
simpl.
rewrite rev_app_distr.
simpl.
unfold value.
repeat f_equal.
find_apply_lem_hyp applyEntries_execute_log'.
repeat find_rewrite.
simpl in *.
repeat find_rewrite.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_same in *.
find_inversion.
auto.
+
unfold applyEntry in *.
break_let.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_diff in *; auto.
copy_eapply_prop_hyp applyEntries applyEntries; [| match goal with | H : context [id] |- _ => apply H end].
intuition.
right.
break_exists_name e; exists e.
break_exists_name xs.
exists xs.
break_exists_name ys.
break_exists.
intuition.
subst.
match goal with | _ : deduplicate_log' ?l ?ks = _ |- _ => pose proof deduplicate_log'_app l [x] ks end.
repeat find_rewrite.
repeat eexists; eauto.
rewrite app_ass.
rewrite <- app_comm_cons.
eauto.
-
do_bool.
subst.
destruct (clientId_eq_dec (eClient x) client).
+
subst.
assert (id = eId x).
{
unfold applyEntry in *.
break_let.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_same in *.
find_inversion.
auto.
}
subst.
right.
unfold applyEntry in *.
break_let.
find_inversion.
exists x, (deduplicate_log' l (clientCache_to_ks (clientCache st))), [].
intuition.
*
rewrite deduplicate_log'_app.
f_equal.
simpl in *.
repeat break_match; auto.
do_bool.
find_apply_lem_hyp applyEntries_log_to_ks'.
find_apply_lem_hyp a_equiv_sym.
find_erewrite_lem assoc_a_equiv; eauto.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
repeat find_rewrite.
congruence.
*
rewrite execute_log'_app.
break_let.
simpl in *.
break_let.
simpl.
rewrite rev_app_distr.
simpl.
unfold value.
repeat f_equal.
find_apply_lem_hyp applyEntries_execute_log'.
repeat find_rewrite.
simpl in *.
repeat find_rewrite.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_same in *.
find_inversion.
auto.
+
unfold applyEntry in *.
break_let.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_diff in *; auto.
copy_eapply_prop_hyp applyEntries applyEntries; [| match goal with | H : context [id] |- _ => apply H end].
intuition.
right.
break_exists_name e; exists e.
break_exists_name xs.
exists xs.
break_exists_name ys.
break_exists.
intuition.
subst.
match goal with | _ : deduplicate_log' ?l ?ks = _ |- _ => pose proof deduplicate_log'_app l [x] ks end.
repeat find_rewrite.
repeat eexists; eauto.
rewrite app_ass.
rewrite <- app_comm_cons.
Admitted.

Lemma doGenericServer_spec : forall (orig_base_params : BaseParams) (one_node_params : OneNodeParams orig_base_params) (raft_params : RaftParams orig_base_params) (h : name) (st : raft_data) (os : list raft_output) (st' : raft_data) (ps : list (name * msg)), doGenericServer h st = (os, st', ps) -> st' = st \/ log st' = log st /\ lastApplied st < lastApplied st' /\ lastApplied st' = commitIndex st /\ exists os' st'', applyEntries h st (rev (filter (fun x : entry => (lastApplied st <? eIndex x) && (eIndex x <=? commitIndex st)) (findGtIndex (log st) (lastApplied st)))) = (os', st'') /\ clientCache st' = clientCache st'' /\ forall c, getLastId st' c = getLastId st'' c.
Proof using.
intros.
unfold doGenericServer in *.
break_let.
break_if.
-
right.
do_bool.
find_inversion.
simpl in *.
intuition; eauto; use_applyEntries_spec; subst; simpl in *; auto.
-
left.
do_bool.
find_inversion.
match goal with | _ : applyEntries _ _ (rev ?l) = _ |- _ => enough (l = []) by (repeat find_rewrite; simpl in *; find_inversion; destruct r; simpl in *; auto) end.
erewrite filter_fun_ext_eq; eauto using filter_false.
intros.
simpl in *.
apply Bool.not_true_is_false.
intuition.
do_bool.
intuition.
do_bool.
use_applyEntries_spec.
subst.
simpl in *.
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
rewrite assoc_default_assoc_set_diff; auto.

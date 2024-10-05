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

Lemma deduplicate_log_app : forall l l', exists l'', deduplicate_log (l ++ l') = deduplicate_log l ++ l''.
Proof using.
Admitted.

Lemma output_correct_monotonic : forall c i o xs ys, output_correct c i o xs -> output_correct c i o (xs ++ ys).
Proof using.
unfold output_correct.
intros.
break_exists.
intuition.
pose proof (deduplicate_log_app xs ys).
break_exists.
repeat find_rewrite.
rewrite app_ass in *.
simpl in *.
eexists.
eexists.
eexists.
eexists.
eexists.
Admitted.

Lemma execute_log'_trace: forall l d d' tr tr' tr'', execute_log' l d tr = (tr', d') -> execute_log' l d (tr'' ++ tr) = (tr'' ++ tr', d').
Proof using.
induction l; intros; simpl in *.
-
find_inversion.
auto.
-
repeat break_let.
rewrite app_ass.
Admitted.

Lemma execute_log'_trace_nil: forall l d d' tr' tr'', execute_log' l d [] = (tr', d') -> execute_log' l d tr'' = (tr'' ++ tr', d').
Proof using.
intros.
Admitted.

Lemma hd_error_Some_app : forall A l l' (x : A), hd_error l = Some x -> hd_error (l ++ l') = Some x.
Proof using.
intros.
Admitted.

Lemma client_cache_keys_correct_do_generic_server : raft_net_invariant_do_generic_server' client_cache_keys_correct.
Proof using si.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_apply_lem_hyp doGenericServer_spec.
intuition; repeat find_rewrite; eauto.
break_exists.
intuition.
find_apply_lem_hyp applyEntries_log_to_ks'.
repeat find_rewrite.
eapply a_equiv_trans; eauto.
get_invariant_pre logs_sorted_invariant.
unfold logs_sorted in *; intuition.
erewrite removeAfterIndex_app; eauto.
rewrite rev_app_distr.
rewrite log_to_ks'_app.
match goal with | |- a_equiv _ (_ (_ ?l) _) (_ (_ ?l') _) => enough (l = l') by (repeat find_rewrite; now apply log_to_ks'_a_equiv) end.
apply filter_fun_ext_eq.
intros.
rewrite <- Bool.andb_true_l.
f_equal.
apply Nat.ltb_lt.
find_apply_lem_hyp findGtIndex_necessary.
Admitted.

Lemma client_cache_keys_correct_append_entries : raft_net_invariant_append_entries' client_cache_keys_correct.
Proof using lmi smsi misi si.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleAppendEntries_clientCache; eauto.
Admitted.

Lemma client_cache_keys_correct_append_entries_reply : raft_net_invariant_append_entries_reply' client_cache_keys_correct.
Proof using.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleAppendEntriesReply_clientCache; eauto.
erewrite handleAppendEntriesReply_log; eauto.
Admitted.

Lemma client_cache_keys_correct_request_vote : raft_net_invariant_request_vote' client_cache_keys_correct.
Proof using.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleRequestVote_clientCache; eauto.
erewrite handleRequestVote_same_log; eauto.
Admitted.

Lemma client_cache_keys_correct_request_vote_reply : raft_net_invariant_request_vote_reply' client_cache_keys_correct.
Proof using.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleRequestVoteReply_clientCache; eauto.
erewrite handleRequestVoteReply_log; eauto.
Admitted.

Lemma client_cache_keys_correct_client_request : raft_net_invariant_client_request' client_cache_keys_correct.
Proof using misi.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleClientRequest_clientCache; eauto.
Admitted.

Lemma client_cache_keys_correct_timeout : raft_net_invariant_timeout' client_cache_keys_correct.
Proof using.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleTimeout_clientCache; eauto.
erewrite handleTimeout_lastApplied; eauto.
Admitted.

Lemma client_cache_keys_correct_do_leader : raft_net_invariant_do_leader' client_cache_keys_correct.
Proof using.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite doLeader_clientCache; eauto.
erewrite doLeader_lastApplied; eauto.
Admitted.

Lemma client_cache_keys_correct_reboot : raft_net_invariant_reboot' client_cache_keys_correct.
Proof using.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
Admitted.

Lemma client_cache_keys_correct_state_same_packet_subset : raft_net_invariant_state_same_packet_subset client_cache_keys_correct.
Proof using.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_reverse_higher_order_rewrite.
Admitted.

Lemma client_cache_keys_correct_init : raft_net_invariant_init client_cache_keys_correct.
Proof using.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
Admitted.

Lemma state_machine_do_generic_server : raft_net_invariant_do_generic_server' state_machine_log.
Proof using lmi smsi misi si.
red.
unfold state_machine_log in *.
simpl in *.
intros.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
unfold doGenericServer in *.
break_let.
find_inversion.
simpl in *.
find_copy_apply_lem_hyp applyEntries_execute_log'.
repeat find_rewrite.
find_copy_apply_lem_hyp applyEntries_lastApplied_commitIndex_log.
break_and.
repeat find_rewrite.
simpl in *.
repeat find_higher_order_rewrite.
break_if; do_bool.
-
rewrite filter_and by (intros; match goal with | |- context [?x <? ?y] => destruct (x <? y) eqn:?; auto end; do_bool; find_eapply_lem_hyp findGtIndex_necessary; omega).
get_invariant_pre logs_sorted_invariant; unfold logs_sorted in *; intuition.
match goal with | |- context [commitIndex ?st] => rewrite removeAfterIndex_app with (i := commitIndex st) (i' := lastApplied st); intuition eauto end.
rewrite rev_app_distr.
unfold deduplicate_log.
rewrite deduplicate_log'_app.
unfold execute_log.
rewrite execute_log'_app.
break_let.
simpl in *.
erewrite snd_execute_log'.
f_equal.
f_equal.
apply deduplicate_log'_a_equiv.
apply client_cache_keys_correct_invariant; auto.
-
match goal with | |- context [filter ?f ?l] => assert (filter f l = filter (fun _ => false) l) by (apply filter_fun_ext_eq; intros; do_bool; right; apply leb_correct_conv; eapply le_lt_trans; eauto; eapply findGtIndex_necessary; eauto) end.
repeat find_rewrite.
rewrite filter_false.
Admitted.

Lemma state_machine_append_entries : raft_net_invariant_append_entries' state_machine_log.
Proof using lmi smsi misi si.
red.
unfold state_machine_log in *.
simpl in *.
intros.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleAppendEntries_stateMachine; eauto.
Admitted.

Lemma state_machine_append_entries_reply : raft_net_invariant_append_entries_reply' state_machine_log.
Proof using.
red.
unfold state_machine_log in *.
simpl in *.
intros.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleAppendEntriesReply_stateMachine; eauto.
erewrite handleAppendEntriesReply_log; eauto.
Admitted.

Lemma state_machine_request_vote : raft_net_invariant_request_vote' state_machine_log.
Proof using.
red.
unfold state_machine_log in *.
simpl in *.
intros.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleRequestVote_log; eauto.
erewrite handleRequestVote_same_lastApplied; eauto.
Admitted.

Lemma state_machine_request_vote_reply : raft_net_invariant_request_vote_reply' state_machine_log.
Proof using.
red.
unfold state_machine_log in *.
simpl in *.
intros.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleRequestVoteReply_log; eauto.
erewrite handleRequestVoteReply_same_lastApplied; eauto.
Admitted.

Lemma state_machine_timeout : raft_net_invariant_timeout' state_machine_log.
Proof using.
red.
unfold state_machine_log in *.
simpl in *.
intros.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleTimeout_log_same; eauto.
erewrite handleTimeout_lastApplied; eauto.
Admitted.

Lemma state_machine_client_request : raft_net_invariant_client_request' state_machine_log.
Proof using misi.
red.
unfold state_machine_log in *.
simpl in *.
intros.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleClientRequest_stateMachine; eauto.
Admitted.

Lemma state_machine_do_leader : raft_net_invariant_do_leader' state_machine_log.
Proof using.
red.
unfold state_machine_log in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite doLeader_stateMachine; eauto.
erewrite doLeader_same_log; eauto.
Admitted.

Lemma state_machine_reboot : raft_net_invariant_reboot' state_machine_log.
Proof using.
red.
unfold state_machine_log in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
Admitted.

Lemma state_machine_state_same_packet_subset : raft_net_invariant_state_same_packet_subset state_machine_log.
Proof using.
red.
unfold state_machine_log in *.
simpl in *.
intros.
subst.
find_reverse_higher_order_rewrite.
Admitted.

Lemma state_machine_init : raft_net_invariant_init state_machine_log.
Proof using.
Admitted.

Lemma state_machine_log_invariant : forall net, raft_intermediate_reachable net -> state_machine_log net.
Proof using lmi smsi misi si.
intros.
apply raft_net_invariant'; auto.
-
apply state_machine_init.
-
apply state_machine_client_request.
-
apply state_machine_timeout.
-
apply state_machine_append_entries.
-
apply state_machine_append_entries_reply.
-
apply state_machine_request_vote.
-
apply state_machine_request_vote_reply.
-
apply state_machine_do_leader.
-
apply state_machine_do_generic_server.
-
apply state_machine_state_same_packet_subset.
-
Admitted.

Lemma client_cache_correct_do_generic_server : raft_net_invariant_do_generic_server' client_cache_correct.
Proof using lmi smsi misi si.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
repeat find_rewrite.
find_apply_lem_hyp doGenericServer_spec.
intuition; repeat find_rewrite; eauto.
get_invariant_pre logs_sorted_invariant.
unfold logs_sorted in *.
intuition.
erewrite removeAfterIndex_app; eauto.
break_exists.
intuition.
find_higher_order_rewrite.
find_eapply_lem_hyp applyEntries_execute_log'_cache; eauto.
intuition.
-
find_apply_hyp_hyp.
rewrite rev_app_distr.
eauto using output_correct_monotonic.
-
unfold output_correct.
break_exists.
intuition.
rewrite rev_app_distr.
unfold deduplicate_log.
rewrite deduplicate_log'_app.
match goal with | _ : context [execute_log' ?x ?y] |- _ => destruct (execute_log' x y) eqn:? end.
simpl in *.
match goal with | [ H : deduplicate_log' _ _ = ?xs ++ ?e :: ?ys |- context [?l ++ deduplicate_log' _ _] ] => (exists (l ++ xs), e, ys) end.
unfold execute_log.
repeat rewrite app_ass.
rewrite execute_log'_app.
break_let.
get_invariant_pre state_machine_log_invariant.
unfold state_machine_log in *.
repeat find_higher_order_rewrite.
unfold execute_log, deduplicate_log in *.
repeat find_rewrite.
simpl in *.
match goal with | [ H : execute_log' (_ ++ _) _ _ = (?tr, ?st) |- context [execute_log' _ _ ?tr'] ] => (exists (tr' ++ tr), st) end.
intuition.
+
f_equal.
repeat find_reverse_rewrite.
match goal with | H : deduplicate_log' _ _ = _ ++ _ :: _ |- _ => clear H end.
match goal with | |- _ ?l _ = _ ?l' _ => assert (l = l') by (f_equal; apply filter_fun_ext_eq; intros; repeat find_rewrite; rewrite <- Bool.andb_true_l at 1; f_equal; symmetry; apply Nat.ltb_lt; find_apply_lem_hyp findGtIndex_necessary; intuition) end.
repeat find_rewrite.
apply deduplicate_log'_a_equiv.
apply a_equiv_sym.
apply client_cache_keys_correct_invariant; auto.
+
eauto using execute_log'_trace_nil.
+
rewrite rev_app_distr.
Admitted.

Lemma same_clientCache_same_getLastId : forall st st' k, clientCache st = clientCache st' -> getLastId st k = getLastId st' k.
Proof using.
intros.
unfold getLastId in *.
find_rewrite.
Admitted.

Lemma client_cache_correct_append_entries : raft_net_invariant_append_entries' client_cache_correct.
Proof using lmi smsi misi si.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache handleAppendEntries_clientCache.
Admitted.

Lemma client_cache_correct_append_entries_reply : raft_net_invariant_append_entries_reply' client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache handleAppendEntriesReply_clientCache.
erewrite handleAppendEntriesReply_log; eauto.
Admitted.

Lemma client_cache_correct_request_vote : raft_net_invariant_request_vote' client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache handleRequestVote_clientCache.
erewrite handleRequestVote_same_log; eauto.
Admitted.

Lemma client_cache_correct_request_vote_reply : raft_net_invariant_request_vote_reply' client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache handleRequestVoteReply_clientCache.
erewrite handleRequestVoteReply_log; eauto.
Admitted.

Lemma client_cache_correct_client_request : raft_net_invariant_client_request' client_cache_correct.
Proof using misi.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache handleClientRequest_clientCache.
Admitted.

Lemma client_cache_correct_timeout : raft_net_invariant_timeout' client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache handleTimeout_clientCache.
erewrite handleTimeout_lastApplied; eauto.
Admitted.

Lemma client_cache_keys_correct_invariant: forall (net : network), raft_intermediate_reachable net -> client_cache_keys_correct net.
Proof using lmi smsi misi si.
intros.
apply raft_net_invariant'; auto.
-
apply client_cache_keys_correct_init.
-
apply client_cache_keys_correct_client_request.
-
apply client_cache_keys_correct_timeout.
-
apply client_cache_keys_correct_append_entries.
-
apply client_cache_keys_correct_append_entries_reply.
-
apply client_cache_keys_correct_request_vote.
-
apply client_cache_keys_correct_request_vote_reply.
-
apply client_cache_keys_correct_do_leader.
-
apply client_cache_keys_correct_do_generic_server.
-
apply client_cache_keys_correct_state_same_packet_subset.
-
apply client_cache_keys_correct_reboot.

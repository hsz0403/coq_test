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
erewrite doLeader_lastApplied; eauto.

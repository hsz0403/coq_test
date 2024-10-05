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
erewrite doLeader_log; eauto.

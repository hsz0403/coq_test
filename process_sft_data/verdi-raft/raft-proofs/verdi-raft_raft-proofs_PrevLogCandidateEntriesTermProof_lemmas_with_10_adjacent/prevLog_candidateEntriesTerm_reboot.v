Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RefinementCommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.PrevLogCandidateEntriesTermInterface.
Section PrevLogCandidateEntriesTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cei : candidate_entries_interface}.
Context {cti : cronies_term_interface}.
Context {cci : cronies_correct_interface}.
Instance plceti : prevLog_candidateEntriesTerm_interface.
Proof.
constructor.
apply prevLog_candidateEntriesTerm_invariant.
End PrevLogCandidateEntriesTerm.

Lemma prevLog_candidateEntriesTerm_request_vote : refined_raft_net_invariant_request_vote prevLog_candidateEntriesTerm.
Proof using.
unfold refined_raft_net_invariant_request_vote, prevLog_candidateEntriesTerm.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
-
find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
eapply candidateEntriesTerm_ext; eauto.
eapply handleRequestVote_preserves_candidateEntriesTerm; eauto.
-
exfalso.
eapply handleRequestVote_no_append_entries; eauto.
simpl in *.
subst.
Admitted.

Lemma handleRequestVoteReply_preserves_candidateEntriesTerm : forall net h h' t r st' t', handleRequestVoteReply h (snd (nwState net h)) h' t r = st' -> refined_raft_intermediate_reachable net -> candidateEntriesTerm t' (nwState net) -> candidateEntriesTerm t' (update name_eq_dec (nwState net) h (update_elections_data_requestVoteReply h h' t r (nwState net h), st')).
Proof using cci.
unfold candidateEntriesTerm.
intros.
break_exists_exists.
update_destruct_simplify; auto.
break_and.
unfold raft_data in *.
simpl in *.
unfold update_elections_data_requestVoteReply.
match goal with | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] => remember (handleRequestVoteReply h st h' t r) as new_state end; find_copy_apply_lem_hyp handleRequestVoteReply_spec.
repeat (break_match); intuition; repeat find_rewrite; intuition; simpl; break_if; auto.
-
find_apply_lem_hyp cronies_correct_invariant.
unfold cronies_correct in *.
intuition.
unfold votes_received_leaders in *.
match goal with | H : Leader = _ |- _ => symmetry in H end.
find_apply_hyp_hyp.
eapply wonElection_no_dup_in; eauto using NoDup_dedup, in_dedup_was_in, dedup_In.
-
destruct (serverType_eq_dec (type (snd (nwState net x))) Leader); intuition.
find_apply_lem_hyp cronies_correct_invariant; auto.
Admitted.

Lemma prevLog_candidateEntriesTerm_request_vote_reply : refined_raft_net_invariant_request_vote_reply prevLog_candidateEntriesTerm.
Proof using cci.
unfold refined_raft_net_invariant_request_vote_reply, prevLog_candidateEntriesTerm.
simpl.
intros.
find_apply_hyp_hyp.
find_eapply_lem_hyp app_cons_in_rest; [|solve[eauto]].
eapply candidateEntriesTerm_ext; eauto.
subst.
Admitted.

Lemma doLeader_preserves_candidateEntriesTerm : forall net gd d h os d' ms t', nwState net h = (gd, d) -> doLeader d h = (os, d', ms) -> candidateEntriesTerm t' (nwState net) -> candidateEntriesTerm t' (update name_eq_dec (nwState net) h (gd, d')).
Proof using.
unfold candidateEntriesTerm.
intros.
break_exists_exists.
break_and.
update_destruct_simplify; auto.
split.
-
match goal with | [ H : nwState ?net ?h = (?x, _) |- _ ] => replace (x) with (fst (nwState net h)) in * by (rewrite H; auto) end.
intuition.
-
match goal with | [ H : nwState ?net ?h = (_, ?x) |- _ ] => replace (x) with (snd (nwState net h)) in * by (rewrite H; auto); clear H end.
find_apply_lem_hyp doLeader_type.
intuition.
subst.
repeat find_rewrite.
Admitted.

Lemma getNextIndex_ext : forall st st' h, nextIndex st' = nextIndex st -> log st' = log st -> getNextIndex st' h = getNextIndex st h.
Proof using.
unfold getNextIndex.
intros.
repeat find_rewrite.
Admitted.

Lemma replicaMessage_ext : forall st st' h h', nextIndex st' = nextIndex st -> log st' = log st -> currentTerm st' = currentTerm st -> commitIndex st' = commitIndex st -> replicaMessage st' h h' = replicaMessage st h h'.
Proof using.
unfold replicaMessage.
intros.
Admitted.

Lemma prevLog_candidateEntriesTerm_do_leader : refined_raft_net_invariant_do_leader prevLog_candidateEntriesTerm.
Proof using cei.
unfold refined_raft_net_invariant_do_leader, prevLog_candidateEntriesTerm.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
-
find_apply_hyp_hyp.
eapply candidateEntriesTerm_ext; eauto.
eapply doLeader_preserves_candidateEntriesTerm; eauto.
-
find_apply_lem_hyp in_map_iff.
break_exists.
break_and.
subst.
simpl in *.
find_copy_eapply_lem_hyp doLeader_messages; eauto.
break_and.
intuition.
+
omega.
+
break_exists.
break_and.
red.
find_apply_lem_hyp candidate_entries_invariant.
unfold CandidateEntries, candidateEntries_host_invariant in *.
find_apply_lem_hyp findAtIndex_elim.
break_and.
match goal with | [ H : nwState ?net ?h = (?y, ?x) |- _ ] => replace (x) with (snd (nwState net h)) in * by (rewrite H; auto); replace (y) with (fst (nwState net h)) in * by (rewrite H; auto) end.
eapply_prop_hyp In In.
subst.
find_eapply_lem_hyp (doLeader_preserves_candidateEntries); eauto.
match goal with | [ H : nwState ?net ?h = (?y, ?x) |- _ ] => clear H end.
unfold candidateEntries in *.
break_exists_exists.
find_higher_order_rewrite.
Admitted.

Lemma doGenericServer_preserves_candidateEntriesTerm : forall net gd d h os d' ms t, nwState net h = (gd, d) -> doGenericServer h d = (os, d', ms) -> candidateEntriesTerm t (nwState net) -> candidateEntriesTerm t (update name_eq_dec (nwState net) h (gd, d')).
Proof using.
intros.
find_apply_lem_hyp doGenericServer_type.
break_and.
eapply candidateEntriesTerm_same; eauto.
-
intros.
update_destruct_simplify; auto.
find_rewrite.
simpl.
auto.
-
intros.
update_destruct_simplify; auto.
repeat find_rewrite.
auto.
-
intros.
update_destruct_simplify; auto.
repeat find_rewrite.
Admitted.

Lemma prevLog_candidateEntriesTerm_do_generic_server : refined_raft_net_invariant_do_generic_server prevLog_candidateEntriesTerm.
Proof using.
unfold refined_raft_net_invariant_do_generic_server, prevLog_candidateEntriesTerm.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
-
eapply candidateEntriesTerm_ext; eauto.
eapply doGenericServer_preserves_candidateEntriesTerm; eauto.
-
find_apply_lem_hyp in_map_iff.
break_exists.
break_and.
subst.
simpl in *.
find_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
Admitted.

Lemma prevLog_candidateEntriesTerm_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset prevLog_candidateEntriesTerm.
Proof using.
unfold refined_raft_net_invariant_state_same_packet_subset, prevLog_candidateEntriesTerm.
simpl.
intros.
find_apply_hyp_hyp.
eapply candidateEntriesTerm_ext with (sigma := (nwState net)).
-
auto.
-
Admitted.

Lemma prevLog_candidateEntriesTerm_invariant : forall net, refined_raft_intermediate_reachable net -> prevLog_candidateEntriesTerm net.
Proof using cci cti cei rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply prevLog_candidateEntriesTerm_init.
-
apply prevLog_candidateEntriesTerm_client_request.
-
apply prevLog_candidateEntriesTerm_timeout.
-
apply prevLog_candidateEntriesTerm_append_entries.
-
apply prevLog_candidateEntriesTerm_append_entries_reply.
-
apply prevLog_candidateEntriesTerm_request_vote.
-
apply prevLog_candidateEntriesTerm_request_vote_reply.
-
apply prevLog_candidateEntriesTerm_do_leader.
-
apply prevLog_candidateEntriesTerm_do_generic_server.
-
apply prevLog_candidateEntriesTerm_state_same_packet_subset.
-
Admitted.

Instance plceti : prevLog_candidateEntriesTerm_interface.
Proof.
constructor.
Admitted.

Lemma prevLog_candidateEntriesTerm_reboot : refined_raft_net_invariant_reboot prevLog_candidateEntriesTerm.
Proof using.
unfold refined_raft_net_invariant_reboot, prevLog_candidateEntriesTerm, reboot.
simpl.
intros.
eapply candidateEntriesTerm_ext; eauto.
repeat find_rewrite.
find_apply_hyp_hyp.
unfold candidateEntriesTerm in *.
break_exists_exists.
update_destruct_simplify; auto.
repeat find_rewrite.
simpl in *.
intuition.
discriminate.

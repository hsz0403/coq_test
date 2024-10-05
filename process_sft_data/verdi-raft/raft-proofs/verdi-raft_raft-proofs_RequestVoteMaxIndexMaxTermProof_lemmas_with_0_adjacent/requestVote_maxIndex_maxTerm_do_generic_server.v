Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RequestVoteMaxIndexMaxTermInterface.
Require Import VerdiRaft.RequestVoteTermSanityInterface.
Section RequestVoteMaxIndexMaxTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {rvrtsi : requestVote_term_sanity_interface}.
Instance rvmimti : requestVote_maxIndex_maxTerm_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply requestVote_maxIndex_maxTerm_init.
-
apply requestVote_maxIndex_maxTerm_client_request.
-
apply requestVote_maxIndex_maxTerm_timeout.
-
apply requestVote_maxIndex_maxTerm_append_entries.
-
apply requestVote_maxIndex_maxTerm_append_entries_reply.
-
apply requestVote_maxIndex_maxTerm_request_vote.
-
apply requestVote_maxIndex_maxTerm_request_vote_reply.
-
apply requestVote_maxIndex_maxTerm_do_leader.
-
apply requestVote_maxIndex_maxTerm_do_generic_server.
-
apply requestVote_maxIndex_maxTerm_state_same_packet_subset.
-
apply requestVote_maxIndex_maxTerm_reboot.
End RequestVoteMaxIndexMaxTerm.

Lemma requestVote_maxIndex_maxTerm_do_generic_server : refined_raft_net_invariant_do_generic_server requestVote_maxIndex_maxTerm.
Proof using.
red.
unfold requestVote_maxIndex_maxTerm.
intros.
simpl in *.
find_copy_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
find_apply_hyp_hyp.
break_or_hyp.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; find_apply_lem_hyp doGenericServer_log_type_term_votesReceived; break_and; repeat find_rewrite; eauto.
intuition.

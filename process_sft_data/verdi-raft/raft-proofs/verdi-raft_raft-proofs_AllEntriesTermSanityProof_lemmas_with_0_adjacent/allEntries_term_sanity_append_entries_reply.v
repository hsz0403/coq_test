Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.AllEntriesTermSanityInterface.
Section AllEntriesTermSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri: raft_refinement_interface}.
Instance aetsi : allEntries_term_sanity_interface.
Proof.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply allEntries_term_sanity_init.
-
apply allEntries_term_sanity_client_request.
-
apply allEntries_term_sanity_timeout.
-
apply allEntries_term_sanity_append_entries.
-
apply allEntries_term_sanity_append_entries_reply.
-
apply allEntries_term_sanity_request_vote.
-
apply allEntries_term_sanity_request_vote_reply.
-
apply allEntries_term_sanity_do_leader.
-
apply allEntries_term_sanity_do_generic_server.
-
apply allEntries_term_sanity_state_same_packet_subset.
-
apply allEntries_term_sanity_reboot.
End AllEntriesTermSanity.

Lemma allEntries_term_sanity_append_entries_reply : refined_raft_net_invariant_append_entries_reply allEntries_term_sanity.
Proof using.
red.
unfold allEntries_term_sanity.
intros.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_apply_lem_hyp handleAppendEntriesReply_type_term.
intuition; repeat find_rewrite; eauto.
find_apply_hyp_hyp.
omega.

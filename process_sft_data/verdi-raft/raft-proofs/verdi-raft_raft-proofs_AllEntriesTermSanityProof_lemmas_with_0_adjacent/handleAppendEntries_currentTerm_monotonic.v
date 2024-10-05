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

Lemma handleAppendEntries_currentTerm_monotonic: forall h st (d : raft_data) (m : msg) (t : term) (n : name) (pli : logIndex) (plt : term) (es : list entry) (ci : logIndex), handleAppendEntries h st t n pli plt es ci = (d, m) -> currentTerm st <= currentTerm d.
Proof using.
intros.
unfold handleAppendEntries in *.
repeat break_match; simpl in *; do_bool; repeat find_inversion; auto; try omega; simpl in *; unfold advanceCurrentTerm in *; repeat break_match; do_bool; auto.

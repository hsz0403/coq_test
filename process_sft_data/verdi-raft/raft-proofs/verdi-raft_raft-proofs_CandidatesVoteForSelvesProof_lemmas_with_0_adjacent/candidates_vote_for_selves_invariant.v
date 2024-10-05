Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.CandidatesVoteForSelvesInterface.
Section CandidatesVoteForSelvesProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Ltac rewrite_state := match goal with | [st : name -> raft_data, H : forall _, ?st _ = _ |- _] => rewrite H in * end.
Ltac t := repeat break_match; simpl in *; try find_inversion; rewrite_state; try use_applyEntries_spec; repeat break_if; subst; eauto; simpl in *; try discriminate.
Instance cvfsi : candidates_vote_for_selves_interface.
Proof.
split.
exact candidates_vote_for_selves_invariant.
End CandidatesVoteForSelvesProof.

Theorem candidates_vote_for_selves_invariant : forall net, raft_intermediate_reachable net -> candidates_vote_for_selves net.
Proof using.
intros.
eapply raft_net_invariant; eauto.
-
apply candidates_vote_for_selves_init.
-
apply candidates_vote_for_selves_client_request.
-
apply candidates_vote_for_selves_timeout.
-
apply candidates_vote_for_selves_append_entries.
-
apply candidates_vote_for_selves_append_entries_reply.
-
apply candidates_vote_for_selves_request_vote.
-
apply candidates_vote_for_selves_request_vote_reply.
-
apply candidates_vote_for_selves_do_leader.
-
apply candidates_vote_for_selves_do_generic_server.
-
apply candidates_vote_for_selves_state_same_packet_subset.
-
apply candidates_vote_for_selves_reboot.

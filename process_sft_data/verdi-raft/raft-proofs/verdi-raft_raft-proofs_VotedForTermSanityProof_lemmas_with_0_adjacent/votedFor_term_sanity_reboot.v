Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RequestVoteTermSanityInterface.
Require Import VerdiRaft.VotedForTermSanityInterface.
Section VotedForTermSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {rvtsi : requestVote_term_sanity_interface}.
Instance vftsi : votedFor_term_sanity_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply votedFor_term_sanity_init.
-
apply votedFor_term_sanity_client_request.
-
apply votedFor_term_sanity_timeout.
-
apply votedFor_term_sanity_append_entries.
-
apply votedFor_term_sanity_append_entries_reply.
-
apply votedFor_term_sanity_request_vote.
-
apply votedFor_term_sanity_request_vote_reply.
-
apply votedFor_term_sanity_do_leader.
-
apply votedFor_term_sanity_do_generic_server.
-
apply votedFor_term_sanity_state_same_packet_subset.
-
apply votedFor_term_sanity_reboot.
End VotedForTermSanity.

Lemma votedFor_term_sanity_reboot : refined_raft_net_invariant_reboot votedFor_term_sanity.
Proof using.
red.
unfold votedFor_term_sanity in *.
intros.
simpl in *.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.

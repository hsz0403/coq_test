Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.CandidateTermGtLogInterface.
Section CandidateTermGtLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {tsi : term_sanity_interface}.
Ltac start := red; unfold candidate_term_gt_log; simpl; intros; find_higher_order_rewrite; update_destruct; subst; rewrite_update; [|auto].
Instance ctgli : candidate_term_gt_log_interface.
Proof.
split.
apply candidate_term_gt_log_invariant.
End CandidateTermGtLog.

Lemma candidate_term_gt_log_invariant : forall net, raft_intermediate_reachable net -> candidate_term_gt_log net.
Proof using tsi.
intros.
apply raft_net_invariant; auto.
-
apply candidate_term_gt_log_init.
-
apply candidate_term_gt_log_client_request.
-
apply candidate_term_gt_log_timeout.
-
apply candidate_term_gt_log_append_entries.
-
apply candidate_term_gt_log_append_entries_reply.
-
apply candidate_term_gt_log_request_vote.
-
apply candidate_term_gt_log_request_vote_reply.
-
apply candidate_term_gt_log_do_leader.
-
apply candidate_term_gt_log_do_generic_server.
-
apply candidate_term_gt_log_state_same_packet_subset.
-
apply candidate_term_gt_log_reboot.

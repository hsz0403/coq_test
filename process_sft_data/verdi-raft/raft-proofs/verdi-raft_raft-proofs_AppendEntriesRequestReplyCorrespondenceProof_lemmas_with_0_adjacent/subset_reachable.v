Require Import FunctionalExtensionality.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Require Import VerdiRaft.AppendEntriesRequestReplyCorrespondenceInterface.
Require Import Verdi.DupDropReordering.
Section AppendEntriesRequestReplyCorrespondence.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance aerrci : append_entries_request_reply_correspondence_interface.
split.
intros.
apply raft_net_invariant; auto.
-
exact append_entries_request_reply_correspondence_init.
-
exact append_entries_request_reply_correspondence_client_request.
-
exact append_entries_request_reply_correspondence_timeout.
-
exact append_entries_request_reply_correspondence_append_entries.
-
exact append_entries_request_reply_correspondence_append_entries_reply.
-
exact append_entries_request_reply_correspondence_request_vote.
-
exact append_entries_request_reply_correspondence_request_vote_reply.
-
exact append_entries_request_reply_correspondence_do_leader.
-
exact append_entries_request_reply_correspondence_do_generic_server.
-
exact append_entries_request_reply_correspondence_state_same_packet_subset.
-
exact append_entries_request_reply_correspondence_reboot.
End AppendEntriesRequestReplyCorrespondence.

Lemma subset_reachable : forall net net', nwState net' = nwState net -> (forall p, In p (nwPackets net') -> In p (nwPackets net)) -> raft_intermediate_reachable net -> raft_intermediate_reachable net'.
Proof using.
intros.
pose proof dup_drop_reorder _ packet_eq_dec _ _ ltac:(eauto).
match goal with | [ H : dup_drop_step_star _ _ _ |- _ ] => eapply step_failure_dup_drop_step with (f := []) (Sigma := nwState net) in H end.
eapply step_failure_star_raft_intermediate_reachable_extend with (f := []) (f' := []) (tr := []); [|eauto].
destruct net, net'.
simpl in *.
subst.
auto.

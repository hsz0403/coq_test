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

Lemma handleAppendEntries_reply_spec: forall h st (d : raft_data) (t : term) (n : name) (pli : logIndex) (plt : term) (es : list entry) (ci : logIndex) (t0 : term) (es0 : list entry) t' es', handleAppendEntries h st t n pli plt es ci = (d, AppendEntriesReply t' es' true) -> t' = t /\ es' = es.
Proof using.
intros.
unfold handleAppendEntries in *.
repeat break_match; find_inversion; auto; congruence.

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

Lemma append_entries_request_reply_correspondence_init : raft_net_invariant_init append_entries_request_reply_correspondence.
Proof using.
red.
unfold append_entries_request_reply_correspondence.
intros.
simpl in *.
intuition.

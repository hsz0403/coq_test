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

Lemma append_entries_request_reply_correspondence_state_same_packet_subset : raft_net_invariant_state_same_packet_subset append_entries_request_reply_correspondence.
Proof using.
red.
unfold append_entries_request_reply_correspondence.
intros.
simpl in *.
find_apply_hyp_hyp.
find_apply_hyp_hyp.
unfold exists_equivalent_network_with_aer in *.
break_exists_name net''.
break_exists_name pli.
break_exists_name plt.
break_exists_name ci.
break_exists_name n.
intuition.
(exists (mkNetwork (nwPackets net' ++ [{| pSrc := pDst p; pDst := pSrc p; pBody := AppendEntries t n pli plt es ci |}]) (nwState net'))).
repeat eexists; intuition; eauto.
repeat find_rewrite.
break_exists_exists; intuition; repeat find_rewrite; eauto.
eapply subset_reachable with (net := net''); eauto.
-
simpl in *.
repeat find_rewrite.
apply functional_extensionality.
eauto.
-
simpl.
intros.
repeat find_rewrite.
do_in_app.
intuition.

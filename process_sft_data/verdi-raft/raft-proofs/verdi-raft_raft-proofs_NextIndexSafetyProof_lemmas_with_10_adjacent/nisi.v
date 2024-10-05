Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Section NextIndexSafety.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {aersi : append_entries_reply_sublog_interface}.
Context {si : sorted_interface}.
Definition nextIndex_preserved st st' := (type st' = Leader -> type st = Leader /\ maxIndex (log st) <= maxIndex (log st') /\ nextIndex st' = nextIndex st).
Instance nisi : nextIndex_safety_interface.
Proof.
split.
exact nextIndex_safety_invariant.
End NextIndexSafety.

Lemma nextIndex_safety_request_vote : raft_net_invariant_request_vote nextIndex_safety.
Proof using.
unfold raft_net_invariant_request_vote, nextIndex_safety.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
eauto using nextIndex_safety_preserved, handleRequestVote_nextIndex_preserved.
-
Admitted.

Lemma handleRequestVoteReply_matchIndex : forall n st src t v, type (handleRequestVoteReply n st src t v) = Leader -> type st = Leader /\ nextIndex (handleRequestVoteReply n st src t v) = nextIndex st \/ nextIndex (handleRequestVoteReply n st src t v) = [].
Proof using.
unfold handleRequestVoteReply.
intros.
Admitted.

Lemma nextIndex_safety_request_vote_reply : raft_net_invariant_request_vote_reply nextIndex_safety.
Proof using.
unfold raft_net_invariant_request_vote_reply, nextIndex_safety.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
find_copy_apply_lem_hyp handleRequestVoteReply_matchIndex.
unfold getNextIndex in *.
erewrite handleRequestVoteReply_log in * by eauto.
intuition; repeat find_rewrite.
+
auto.
+
unfold assoc_default.
simpl.
auto using NPeano.Nat.le_le_pred.
-
Admitted.

Lemma doLeader_nextIndex_preserved : forall st h os st' ms, doLeader st h = (os, st', ms) -> nextIndex_preserved st st'.
Proof using.
unfold doLeader, nextIndex_preserved.
intros.
Admitted.

Lemma nextIndex_safety_do_leader : raft_net_invariant_do_leader nextIndex_safety.
Proof using.
unfold raft_net_invariant_do_leader, nextIndex_safety.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
eauto using nextIndex_safety_preserved, doLeader_nextIndex_preserved.
-
Admitted.

Lemma doGenericServer_nextIndex_preserved : forall h st os st' ms, doGenericServer h st = (os, st', ms) -> nextIndex_preserved st st'.
Proof using.
unfold doGenericServer, nextIndex_preserved.
intros.
Admitted.

Lemma nextIndex_safety_do_generic_server : raft_net_invariant_do_generic_server nextIndex_safety.
Proof using.
unfold raft_net_invariant_do_generic_server, nextIndex_safety.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
eauto using nextIndex_safety_preserved, doGenericServer_nextIndex_preserved.
-
Admitted.

Lemma nextIndex_safety_state_same_packet_subset : raft_net_invariant_state_same_packet_subset nextIndex_safety.
Proof using.
unfold raft_net_invariant_state_same_packet_subset, nextIndex_safety.
simpl.
intros.
repeat find_reverse_higher_order_rewrite.
Admitted.

Lemma nextIndex_safety_reboot : raft_net_invariant_reboot nextIndex_safety.
Proof using.
unfold raft_net_invariant_reboot, nextIndex_safety, reboot.
simpl.
intros.
subst.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
unfold getNextIndex, assoc_default.
simpl.
omega.
-
Admitted.

Lemma nextIndex_safety_invariant : forall net, raft_intermediate_reachable net -> nextIndex_safety net.
Proof using si aersi.
intros.
apply raft_net_invariant; auto.
-
apply nextIndex_safety_init.
-
apply nextIndex_safety_client_request.
-
apply nextIndex_safety_timeout.
-
apply nextIndex_safety_append_entries.
-
apply nextIndex_safety_append_entries_reply.
-
apply nextIndex_safety_request_vote.
-
apply nextIndex_safety_request_vote_reply.
-
apply nextIndex_safety_do_leader.
-
apply nextIndex_safety_do_generic_server.
-
apply nextIndex_safety_state_same_packet_subset.
-
Admitted.

Instance nisi : nextIndex_safety_interface.
Proof.
split.
exact nextIndex_safety_invariant.

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
apply nextIndex_safety_reboot.

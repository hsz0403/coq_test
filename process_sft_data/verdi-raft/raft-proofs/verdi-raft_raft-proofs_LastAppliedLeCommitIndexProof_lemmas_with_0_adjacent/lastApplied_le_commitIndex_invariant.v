Require Import VerdiRaft.Raft.
Require Import VerdiRaft.LastAppliedLeCommitIndexInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section LastAppliedLeCommitIndex.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance lalcii : lastApplied_le_commitIndex_interface.
split.
auto using lastApplied_le_commitIndex_invariant.
End LastAppliedLeCommitIndex.

Theorem lastApplied_le_commitIndex_invariant : forall net, raft_intermediate_reachable net -> lastApplied_le_commitIndex net.
Proof using.
intros.
apply raft_net_invariant; auto.
-
apply lastApplied_le_commitIndex_init.
-
apply lastApplied_le_commitIndex_clientRequest.
-
apply lastApplied_le_commitIndex_timeout.
-
apply lastApplied_le_commitIndex_appendEntries.
-
apply lastApplied_le_commitIndex_appendEntriesReply.
-
apply lastApplied_le_commitIndex_requestVote.
-
apply lastApplied_le_commitIndex_requestVoteReply.
-
apply lastApplied_le_commitIndex_doLeader.
-
apply lastApplied_le_commitIndex_doGenericServer.
-
apply lastApplied_le_commitIndex_state_same_packet_subset.
-
apply lastApplied_le_commitIndex_reboot.

Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.AppendEntriesRequestReplyCorrespondenceInterface.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.AppendEntriesLeaderInterface.
Section AppendEntriesReplySublog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {aerrci : append_entries_request_reply_correspondence_interface}.
Context {rri : raft_refinement_interface}.
Context {aeli : append_entries_leader_interface}.
Definition lowered_appendEntries_leader (net : @network _ multi_params) := forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit h e, In p (nwPackets net) -> pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> In e entries -> currentTerm (nwState net h) = t -> type (nwState net h) = Leader -> In e (log (nwState net h)).
Instance aersi : append_entries_reply_sublog_interface.
split.
exact append_entries_reply_sublog_invariant.
End AppendEntriesReplySublog.

Instance aersi : append_entries_reply_sublog_interface.
split.
exact append_entries_reply_sublog_invariant.

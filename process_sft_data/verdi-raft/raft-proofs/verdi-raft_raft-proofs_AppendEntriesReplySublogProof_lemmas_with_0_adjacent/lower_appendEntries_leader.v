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

Theorem lower_appendEntries_leader : forall net, raft_intermediate_reachable net -> lowered_appendEntries_leader net.
Proof using aeli rri.
intros.
apply (lower_prop lowered_appendEntries_leader); auto.
intros.
find_apply_lem_hyp append_entries_leader_invariant.
unfold lowered_appendEntries_leader, appendEntries_leader in *.
intros.
simpl in *.
repeat break_match.
simpl in *.
do_in_map.
subst.
simpl in *.
match goal with | H : ?nwState ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState h)) in * by (rewrite H; reflexivity); clear H end.
eapply_prop_hyp AppendEntries AppendEntries; eauto.

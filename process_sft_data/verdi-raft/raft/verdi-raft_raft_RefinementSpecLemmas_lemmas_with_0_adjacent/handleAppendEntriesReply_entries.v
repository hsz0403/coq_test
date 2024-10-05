Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Section SpecLemmas.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
End SpecLemmas.

Lemma handleAppendEntriesReply_entries : forall h st t h' pli plt es ci st' t' es', handleAppendEntries h st t h' pli plt es ci = (st', AppendEntriesReply t' es' true) -> t' = t /\ es' = es /\ (forall e, In e es -> In e (log st') \/ haveNewEntries st es = false /\ log st' = log st).
Proof using.
intros.
unfold handleAppendEntries in *.
repeat break_match; find_inversion; simpl in *; intuition; eauto using advanceCurrentTerm_log.

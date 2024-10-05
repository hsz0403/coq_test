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
auto.

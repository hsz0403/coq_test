Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.NoAppendEntriesRepliesToSelfInterface.
Require Import VerdiRaft.NoAppendEntriesToSelfInterface.
Section NoAppendEntriesRepliesToSelf.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {naetsi : no_append_entries_to_self_interface}.
Instance noaertsi : no_append_entries_replies_to_self_interface.
split.
auto using no_append_entries_replies_to_self_invariant.
End NoAppendEntriesRepliesToSelf.

Lemma doLeader_no_messages_to_self : forall st h os st' ms m, doLeader st h = (os, st', ms) -> In m ms -> fst m <> h.
Proof using.
intros.
unfold doLeader in *.
repeat break_match; try solve [find_inversion; simpl in *; congruence].
find_inversion.
do_in_map.
subst.
simpl in *.
find_apply_lem_hyp filter_In.
intuition.
subst.
break_match; congruence.

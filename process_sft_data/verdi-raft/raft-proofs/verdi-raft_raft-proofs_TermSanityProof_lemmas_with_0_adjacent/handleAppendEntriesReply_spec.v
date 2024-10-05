Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TermSanityInterface.
Section TermSanityProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance tsi : term_sanity_interface.
Proof.
split.
auto using no_entries_past_current_term_invariant.
End TermSanityProof.

Lemma handleAppendEntriesReply_spec : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> (currentTerm st <= currentTerm st' /\ log st' = log st /\ (forall m, In m ms -> ~ is_append_entries (snd m))).
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
repeat break_match; try find_inversion; subst; simpl in *; intuition; do_bool; intuition; try solve [break_exists; congruence]; in_crush; eauto using removeAfterIndex_in.

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

Lemma handleRequestVote_spec : forall h st t h' pli plt st' m, handleRequestVote h st t h' pli plt = (st', m) -> (currentTerm st <= currentTerm st' /\ log st' = log st /\ ~ is_append_entries m).
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
repeat break_match; try find_inversion; subst; simpl in *; intuition; do_bool; intuition; try solve [break_exists; congruence]; in_crush; eauto using removeAfterIndex_in.

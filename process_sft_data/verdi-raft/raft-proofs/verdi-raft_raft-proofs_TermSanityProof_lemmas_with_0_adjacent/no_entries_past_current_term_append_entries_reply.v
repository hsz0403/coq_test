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

Lemma no_entries_past_current_term_append_entries_reply : raft_net_invariant_append_entries_reply no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_append_entries_reply.
intros.
find_apply_lem_hyp handleAppendEntriesReply_spec.
intuition eauto using no_entries_past_current_term_unaffected.

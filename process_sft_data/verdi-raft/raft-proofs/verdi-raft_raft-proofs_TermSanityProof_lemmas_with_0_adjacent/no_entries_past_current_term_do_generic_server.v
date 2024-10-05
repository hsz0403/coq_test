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

Lemma no_entries_past_current_term_do_generic_server : raft_net_invariant_do_generic_server no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_do_generic_server, no_entries_past_current_term.
intros.
find_apply_lem_hyp doGenericServer_spec.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_higher_order_rewrite; break_match; eauto.
subst; repeat find_rewrite; eauto.
-
eauto using no_entries_past_current_term_nw_no_append_entries.

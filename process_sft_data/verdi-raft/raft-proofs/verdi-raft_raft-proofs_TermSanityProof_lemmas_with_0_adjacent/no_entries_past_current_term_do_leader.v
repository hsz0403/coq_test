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

Theorem no_entries_past_current_term_do_leader : raft_net_invariant_do_leader (no_entries_past_current_term).
Proof using.
unfold raft_net_invariant_do_leader, no_entries_past_current_term.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_apply_lem_hyp doLeader_spec.
find_higher_order_rewrite.
break_if; subst; intuition; repeat find_rewrite; eauto.
-
unfold no_entries_past_current_term_nw in *.
intros; simpl in *.
find_apply_hyp_hyp.
intuition eauto.
unfold doLeader in *.
repeat break_match; repeat find_inversion; try solve_by_inversion.
repeat do_in_map; subst; simpl in *; find_inversion.
find_apply_lem_hyp findGtIndex_in.
eauto.

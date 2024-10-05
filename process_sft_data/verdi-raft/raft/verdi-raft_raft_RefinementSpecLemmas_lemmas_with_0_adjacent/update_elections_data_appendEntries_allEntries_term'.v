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

Lemma update_elections_data_appendEntries_allEntries_term' : forall h st t h' pli plt es ci te e d m, In (te, e) (allEntries (update_elections_data_appendEntries h st t h' pli plt es ci)) -> handleAppendEntries h (snd st) t h' pli plt es ci = (d, m) -> In (te, e) (allEntries (fst st)) \/ (In e es /\ te = currentTerm d).
Proof using.
intros.
unfold update_elections_data_appendEntries in *.
repeat break_match; subst; simpl in *; auto.
unfold handleAppendEntries, advanceCurrentTerm in *.
repeat break_match; simpl in *; repeat find_inversion; do_bool; simpl in *; auto; try (do_in_app; intuition; do_in_map; repeat find_inversion; subst; simpl in *; auto); find_eapply_lem_hyp Nat.le_antisymm; eauto.

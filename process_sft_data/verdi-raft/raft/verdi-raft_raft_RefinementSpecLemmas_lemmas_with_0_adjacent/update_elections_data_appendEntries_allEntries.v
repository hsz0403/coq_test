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

Lemma update_elections_data_appendEntries_allEntries : forall h st t h' pli plt es ci e, In e (map snd (allEntries (update_elections_data_appendEntries h st t h' pli plt es ci))) -> In e (map snd (allEntries (fst st))) \/ In e es.
Proof using.
intros.
unfold update_elections_data_appendEntries in *.
repeat break_match; subst; simpl in *; auto.
find_apply_lem_hyp handleAppendEntriesReply_entries.
subst.
do_in_map.
do_in_app.
subst.
intuition.
-
do_in_map.
subst.
simpl in *.
auto.
-
left.
apply in_map_iff.
eexists; eauto.

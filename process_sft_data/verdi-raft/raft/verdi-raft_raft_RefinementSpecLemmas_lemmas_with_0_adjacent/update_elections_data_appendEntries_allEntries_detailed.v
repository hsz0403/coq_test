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

Lemma update_elections_data_appendEntries_allEntries_detailed : forall h st t h' pli plt es ci st' m te e, handleAppendEntries h (snd st) t h' pli plt es ci = (st', m) -> In (te, e) (allEntries (update_elections_data_appendEntries h st t h' pli plt es ci)) -> In (te, e) (allEntries (fst st)) \/ In e (log st') \/ (In e es /\ haveNewEntries (snd st) es = false /\ log st' = log (snd st)).
Proof using.
intros.
unfold update_elections_data_appendEntries in *.
repeat break_match; subst; simpl in *; auto.
find_apply_lem_hyp handleAppendEntriesReply_entries.
intuition.
find_inversion.
do_in_app.
intuition.
do_in_map.
find_inversion.
find_copy_apply_hyp_hyp.
intuition.

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

Lemma update_elections_data_clientRequest_allEntries_new : forall h st client id c e, In e (map snd (allEntries (update_elections_data_client_request h st client id c))) -> In e (map snd (allEntries (fst st))) \/ (eIndex e = S (maxIndex (log (snd st))) /\ eTerm e = currentTerm (snd st) /\ type (snd st) = Leader).
Proof using.
intros.
unfold update_elections_data_client_request in *.
repeat break_match; subst; simpl in *; auto.
intuition.
subst.
do_bool.
find_apply_lem_hyp handleClientRequest_log.
intuition.
-
match goal with | H : log _ = log (snd _) |- _ => symmetry in H end.
repeat find_rewrite.
simpl in *.
omega.
-
break_exists.
intuition.
repeat find_rewrite.
find_inversion.
intuition.

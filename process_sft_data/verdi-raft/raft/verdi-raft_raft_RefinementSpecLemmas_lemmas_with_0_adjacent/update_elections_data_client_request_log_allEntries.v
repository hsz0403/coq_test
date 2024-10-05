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

Lemma update_elections_data_client_request_log_allEntries : forall h st client id c out st' ms, handleClientRequest h (snd st) client id c = (out, st', ms) -> (allEntries (update_elections_data_client_request h st client id c) = allEntries (fst st) /\ log st' = log (snd st)) \/ (type (snd st) = Leader /\ exists e : entry, eIndex e = S (maxIndex (log (snd st))) /\ eTerm e = currentTerm (snd st) /\ eClient e = client /\ eInput e = c /\ eId e = id /\ type (snd st) = Leader /\ allEntries (update_elections_data_client_request h st client id c) = (currentTerm st', e) :: allEntries (fst st) /\ log st' = e :: log (snd st)).
Proof using.
intros.
unfold update_elections_data_client_request.
unfold handleClientRequest in *.
repeat break_match; repeat tuple_inversion; auto.
-
discriminate.
-
do_bool.
find_rewrite.
omega.
-
do_bool.
find_rewrite.
omega.
-
simpl in *.
right.
intuition.
exists e.
find_inversion.
simpl.
intuition.
-
simpl in *.
do_bool.
omega.

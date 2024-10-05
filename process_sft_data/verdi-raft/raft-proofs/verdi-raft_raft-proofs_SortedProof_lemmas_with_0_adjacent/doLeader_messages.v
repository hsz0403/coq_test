Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.SortedInterface.
Section SortedProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {tsi : term_sanity_interface}.
Ltac find_eapply_hyp_goal := match goal with | H : _ |- _ => eapply H end.
Instance si : sorted_interface.
Proof.
split.
eauto using handleAppendEntries_logs_sorted.
eauto using handleClientRequest_logs_sorted.
auto using logs_sorted_invariant.
End SortedProof.

Lemma doLeader_messages : forall h st os st' ms m t n pli plt entries c, doLeader st h = (os, st', ms) -> sorted (log st) -> In m ms -> snd m = AppendEntries t n pli plt entries c -> subseq entries (log st) /\ (forall e, In e entries -> eIndex e > pli) /\ (forall e, In e entries -> eTerm e >= plt).
Proof using.
intros.
unfold doLeader in *.
repeat break_match; find_inversion; subst; simpl in *; intuition.
-
unfold replicaMessage in *.
do_in_map.
simpl in *.
subst.
simpl in *.
find_inversion.
apply subseq_findGtIndex.
-
unfold replicaMessage in *.
do_in_map.
simpl in *.
subst.
simpl in *.
find_inversion.
find_apply_lem_hyp findGtIndex_necessary; intuition.
-
unfold replicaMessage in *.
do_in_map.
simpl in *.
subst.
simpl in *.
find_inversion.
break_match; intuition.
find_apply_lem_hyp findGtIndex_necessary; intuition.
find_apply_lem_hyp findAtIndex_elim.
simpl in *.
intuition.
repeat find_rewrite.
eapply sorted_index_term; eauto.
omega.

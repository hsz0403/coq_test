Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CandidatesVoteForSelvesInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Section CroniesCorrectProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {vci : votes_correct_interface}.
Context {cvfsi : candidates_vote_for_selves_interface}.
Instance cci : cronies_correct_interface.
Proof.
split.
auto using cronies_correct_invariant.
End CroniesCorrectProof.

Lemma cronies_correct_do_generic_server : refined_raft_net_invariant_do_generic_server cronies_correct.
Proof using.
unfold refined_raft_net_invariant_do_generic_server.
intros.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold doGenericServer in *.
repeat break_match; find_inversion; subst; simpl in *; eauto; match goal with | H : ?t = (?x, ?y) |- context [ ?x ] => assert (x = (fst t)) by (rewrite H; reflexivity); assert (y = (snd t)) by (rewrite H; reflexivity); clear H; subst end; use_applyEntries_spec; subst; simpl in *; intuition eauto.
-
unfold cronies_votes in *.
intros.
simpl in *.
find_higher_order_rewrite.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto; try match goal with | H : ?t = (?x, ?y) |- _ => assert (x = (fst t)) by (rewrite H; reflexivity); assert (y = (snd t)) by (rewrite H; reflexivity); clear H; subst end; intuition eauto.
-
unfold votes_nw in *.
intros.
simpl in *.
find_eapply_lem_hyp do_generic_server_pkts; eauto.
find_apply_hyp_hyp.
find_higher_order_rewrite.
repeat break_if; subst; simpl in *; auto; find_rewrite; simpl in *; auto.
-
unfold votes_received_leaders in *.
intros.
simpl in *.
find_higher_order_rewrite.
unfold doGenericServer in *.
repeat break_match; repeat find_inversion; subst; simpl in *; use_applyEntries_spec; subst; simpl in *; eauto; match goal with | H : nwState ?x1 ?x2 = (?x, ?y) |- _ => assert (y = (snd (nwState x1 x2))) by (rewrite H; reflexivity); clear H; subst end; intuition eauto.

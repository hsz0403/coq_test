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

Lemma cronies_correct_do_leader : refined_raft_net_invariant_do_leader cronies_correct.
Proof using.
unfold refined_raft_net_invariant_do_leader.
intros.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies in *.
simpl in *.
intros.
find_apply_lem_hyp doLeader_st.
repeat find_higher_order_rewrite.
repeat break_match; simpl in *; repeat find_rewrite; intuition eauto; repeat find_rewrite; match goal with | _ : nwState _ ?h = _, H : forall _ _ : name, _ |- _ => specialize (H h) end; repeat find_rewrite; simpl in *; intuition eauto.
-
unfold cronies_votes in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
repeat break_if; simpl in *; subst; eauto; match goal with | [ H : forall (_ : term) (_ _ : name), _ |- In (?t, ?h) _ ] => specialize (H t h) end; repeat find_rewrite; simpl in *; find_apply_hyp_hyp; repeat find_rewrite; intuition eauto.
-
unfold votes_nw in *.
intros.
simpl in *.
find_eapply_lem_hyp do_leader_rvr; eauto.
find_apply_hyp_hyp.
find_higher_order_rewrite.
break_if; auto; subst; simpl in *; repeat find_rewrite; simpl in *; auto.
-
unfold votes_received_leaders in *.
intros.
find_apply_lem_hyp doLeader_st.
intuition.
find_higher_order_rewrite.
simpl in *.
repeat break_if; simpl in *; subst; eauto.
repeat find_rewrite.
match goal with | H : ?t = (?x, ?y) |- context [ ?y ] => assert (y = (snd t)) by (rewrite H; reflexivity); clear H; subst end.
eauto.

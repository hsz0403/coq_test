Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.VotesVotesWithLogCorrespondInterface.
Section VotesVotesWithLogCorrespond.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Ltac start := red; intros; eapply votes_votesWithLog_correspond_cases; eauto.
Ltac finish := repeat break_match; subst_max; first [ left; solve[eauto] | right; repeat eexists; solve[eauto] ].
Ltac unfold_all := red; unfold votes_votesWithLog_correspond, votes_votesWithLog, votesWithLog_votes.
Instance vvci : votes_votesWithLog_correspond_interface.
Proof.
split.
exact votes_votesWithLog_correspond_invariant.
Defined.
End VotesVotesWithLogCorrespond.

Lemma votes_votesWithLog_correspond_invariant : forall net, refined_raft_intermediate_reachable net -> votes_votesWithLog_correspond net.
Proof using rri.
intros.
apply refined_raft_net_invariant; auto.
-
unfold_all.
simpl.
split; contradiction.
-
start.
unfold update_elections_data_client_request in *.
finish.
-
start.
unfold update_elections_data_timeout in *.
finish.
-
start.
unfold update_elections_data_appendEntries in *.
finish.
-
start.
subst; auto.
-
start.
unfold update_elections_data_requestVote in *.
finish.
-
start.
unfold update_elections_data_requestVoteReply in *.
finish.
-
start.
find_rewrite.
auto.
-
start.
find_rewrite.
auto.
-
unfold_all.
split; intros; break_and; repeat find_reverse_higher_order_rewrite; eauto.
-
unfold_all.
intuition; find_higher_order_rewrite; (update_destruct; subst; rewrite_update; [|eauto]); unfold reboot in *; simpl in *; (eapply equates_1; [ match goal with | H : _ |- _ => solve [ eapply H; aggressive_rewrite_goal; eauto ] end |]); find_rewrite; auto.

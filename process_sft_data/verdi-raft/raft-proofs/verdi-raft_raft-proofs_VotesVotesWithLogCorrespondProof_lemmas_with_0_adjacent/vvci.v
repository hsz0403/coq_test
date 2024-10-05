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

Instance vvci : votes_votesWithLog_correspond_interface.
Proof.
split.
exact votes_votesWithLog_correspond_invariant.

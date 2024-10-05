Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.VotesLeCurrentTermInterface.
Set Bullet Behavior "Strict Subproofs".
Section VotesCorrect.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {vlcti : votes_le_current_term_interface}.
Ltac split_votes_correct := intros; subst; intuition; [ unfold one_vote_per_term in * | unfold votes_currentTerm_votedFor_correct in * | unfold currentTerm_votedFor_votes_correct in * ]; cbn [nwState].
Ltac start_proof := intros; match goal with H : forall _, ?f _ = _ |- _ => rewrite H in * end; update_destruct; rewrite_update; cbn [fst snd] in *; eauto.
Ltac do_le_antisym := match goal with | [ H : ?x <= ?y, H' : ?y <= ?x |- _ ] => assert (x = y) by auto using Nat.le_antisymm end.
Instance vci : votes_correct_interface.
Proof.
split.
auto using votes_correct_invariant.
End VotesCorrect.

Theorem votes_correct_init : refined_raft_net_invariant_init votes_correct.
Proof using.
unfold refined_raft_net_invariant_init, votes_correct.
split_votes_correct; simpl in *; intuition; discriminate.

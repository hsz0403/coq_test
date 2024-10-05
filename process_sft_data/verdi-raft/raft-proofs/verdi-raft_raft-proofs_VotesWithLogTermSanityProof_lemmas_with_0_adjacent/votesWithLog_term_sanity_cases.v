Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.VotesWithLogTermSanityInterface.
Section VotesWithLogTermSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Ltac start := red; unfold votesWithLog_term_sanity; simpl; intros.
Ltac start_update := start; repeat find_higher_order_rewrite; update_destruct; subst; rewrite_update; [|eauto].
Ltac start_cases := red; intros; eapply votesWithLog_term_sanity_cases; eauto.
Ltac solve_votesWithLog lem := intros; subst; first [ left; solve [eapply lem; eauto] | (* votesWithLog doesn't change *) solve [eapply lem; eauto] (* has both cases *) ].
Ltac solve_currentTerm lem := find_apply_lem_hyp lem; solve [intuition].
Instance vwltsi : votesWithLog_term_sanity_interface.
split.
apply votesWithLog_term_sanity_invariant.
Defined.
End VotesWithLogTermSanity.

Lemma votesWithLog_term_sanity_cases : forall net st' ps' h gd d, votesWithLog_term_sanity net -> (forall h' : Net.name, st' h' = update name_eq_dec (nwState net) h (gd, d) h') -> (forall t' h' l', In (t', h', l') (votesWithLog gd) -> In (t', h', l') (votesWithLog (fst (nwState net h))) \/ (t' = currentTerm d /\ l' = log d)) -> currentTerm d >= currentTerm (snd (nwState net h)) -> votesWithLog_term_sanity {| nwPackets := ps'; nwState := st' |}.
Proof using.
unfold votesWithLog_term_sanity.
intros.
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; [|eauto].
simpl in *.
find_apply_hyp_hyp.
break_or_hyp.
-
find_apply_hyp_hyp.
omega.
-
break_and.
subst.
auto.

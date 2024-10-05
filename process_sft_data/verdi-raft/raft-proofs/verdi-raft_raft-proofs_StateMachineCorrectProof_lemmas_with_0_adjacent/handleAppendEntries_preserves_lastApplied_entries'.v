Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.DecompositionWithPostState.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineCorrectInterface.
Section StateMachineCorrect.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {si : sorted_interface}.
Context {misi : max_index_sanity_interface}.
Context {smsi : state_machine_safety_interface}.
Context {lmi : log_matching_interface}.
Ltac get_invariant_pre inv := match goal with | H : raft_intermediate_reachable _ |- _=> match (type of H) with | context [mkNetwork] => fail 2 end || copy_apply inv H end.
Ltac get_invariant_post inv := match goal with | H : raft_intermediate_reachable _ |- _=> match (type of H) with | context [mkNetwork] => copy_apply inv H end end.
Definition clientCache_to_ks (c : list (clientId * (nat * output))) := map (fun e => (fst e, fst (snd e))) c.
Fixpoint log_to_ks' (l : list entry) (ks : list (clientId * nat)) : list (clientId * nat) := match l with | e :: l' => if (assoc_default clientId_eq_dec ks (eClient e) 0) <=? eId e then log_to_ks' l' (assoc_set clientId_eq_dec ks (eClient e) (eId e)) else log_to_ks' l' ks | [] => ks end.
Definition log_to_ks l := log_to_ks' l [].
Definition client_cache_keys_correct net := forall h, a_equiv clientId_eq_dec (clientCache_to_ks (clientCache (nwState net h))) (log_to_ks' (rev (removeAfterIndex (log (nwState net h)) (lastApplied (nwState net h)))) []).
Fixpoint max_id_for_client_default (default : nat) (c : clientId) (l : list entry) : nat := match l with | [] => default | e :: l' => if clientId_eq_dec c (eClient e) then max_id_for_client_default (max default (eId e)) c l' else max_id_for_client_default default c l' end.
Ltac use_same_client_cache hyp := erewrite same_clientCache_same_getLastId in *; [|eapply hyp]; eauto.
Instance smci : state_machine_correct_interface.
Proof.
split.
exact state_machine_correct_invariant.
End StateMachineCorrect.

Lemma handleAppendEntries_preserves_lastApplied_entries': forall (p : packet) (net : network) (d : raft_data) (m : msg) (t : term) (n : name) (pli : logIndex) (plt : term) (es : list entry) (ci : logIndex) xs ys ps' st' e, raft_intermediate_reachable net -> raft_intermediate_reachable {| nwPackets := ps'; nwState := st' |} -> (forall h : name, st' h = update name_eq_dec (nwState net) (pDst p) d h) -> (forall p' : packet, In p' ps' -> In p' (xs ++ ys) \/ p' = {| pSrc := pDst p; pDst := pSrc p; pBody := m |}) -> handleAppendEntries (pDst p) (nwState net (pDst p)) t n pli plt es ci = (d, m) -> nwPackets net = xs ++ p :: ys -> pBody p = AppendEntries t n pli plt es ci -> eIndex e <= lastApplied (nwState net (pDst p)) -> In e (log (nwState net (pDst p))) -> In e (log d).
Proof using lmi smsi misi.
intros.
get_invariant_post max_index_sanity_invariant.
unfold maxIndex_sanity in *; intuition.
unfold maxIndex_lastApplied in *; intuition.
match goal with | H : forall _, lastApplied _ <= maxIndex _ |- _ => specialize (H (pDst p)) end.
simpl in *.
repeat find_higher_order_rewrite.
rewrite_update.
repeat find_rewrite.
get_invariant_pre state_machine_safety_invariant.
unfold state_machine_safety in *.
intuition.
match goal with | H : state_machine_safety_nw _ |- _ => specialize (H (pDst p)) end.
find_copy_apply_lem_hyp handleAppendEntries_log.
intuition; repeat find_rewrite; eauto.
-
match goal with | _ : eIndex ?e <= lastApplied (nwState ?net ?h) |- _ => assert (commit_recorded net h e) by (unfold commit_recorded; eauto) end.
get_invariant_pre log_matching_invariant.
unfold log_matching, log_matching_hosts in *.
intuition.
copy_eapply_prop_hyp In In.
copy_eapply_prop_hyp pBody pBody; eauto.
intuition; try omega.
subst.
find_copy_apply_lem_hyp handleAppendEntries_same_lastApplied.
repeat find_rewrite.
omega.
-
match goal with | _ : eIndex ?e <= lastApplied (nwState ?net ?h) |- _ => assert (commit_recorded net h e) by (unfold commit_recorded; eauto) end.
get_invariant_pre log_matching_invariant.
unfold log_matching, log_matching_hosts in *.
intuition.
copy_eapply_prop_hyp In In.
copy_eapply_prop_hyp pBody pBody; eauto.
intuition.
+
apply in_app_iff.
right.
apply removeAfterIndex_le_In; eauto; omega.
+
apply in_app_iff.
right.
apply removeAfterIndex_le_In; eauto; omega.
+
match goal with | _ : context [maxIndex (?a ++ ?b)] |- _ => pose proof maxIndex_app a b end.
intuition.
repeat find_rewrite.
find_copy_apply_lem_hyp handleAppendEntries_same_lastApplied.
repeat find_rewrite.
omega.

Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Section AppendEntriesRequestLeaderLogs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Context {lmi : log_matching_interface}.
Context {nisi : nextIndex_safety_interface}.
Ltac start := red; unfold append_entries_leaderLogs; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance aerlli : append_entries_leaderLogs_interface.
split.
exact append_entries_leaderLogs_invariant.
End AppendEntriesRequestLeaderLogs.

Lemma doLeader_spec : forall st h os st' ms m t n pli plt es ci, doLeader st h = (os, st', ms) -> In m ms -> snd m = AppendEntries t n pli plt es ci -> t = currentTerm st /\ log st' = log st /\ type st = Leader /\ ((pli = 0 /\ plt = 0 /\ es = findGtIndex (log st) 0) \/ ((exists e, findAtIndex (log st) pli = Some e /\ eTerm e = plt) /\ es = findGtIndex (log st) pli) \/ exists h', pred (getNextIndex st h') <> 0 /\ findAtIndex (log st) (pred (getNextIndex st h')) = None).
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
break_match; try solve [find_inversion; simpl in *; intuition].
break_if; try solve [find_inversion; simpl in *; intuition].
find_inversion.
simpl.
do_in_map.
subst.
simpl in *.
find_inversion.
intuition.
match goal with | |- context [pred ?x] => remember (pred x) as index end.
break_match; simpl in *.
-
right.
left.
eauto.
-
destruct index; intuition.
right.
right.
exists x.
match goal with | _ : S _ = pred ?x |- context [pred ?y] => assert (pred x = pred y) by auto end.
repeat find_rewrite.
intuition.

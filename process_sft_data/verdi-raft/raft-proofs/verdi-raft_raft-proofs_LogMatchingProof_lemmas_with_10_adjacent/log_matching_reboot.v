Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.UniqueIndicesInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.LogMatchingInterface.
Hint Extern 4 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply failure_params : typeclass_instances.
Section LogMatchingProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {si : sorted_interface}.
Context {lsi : leader_sublog_interface}.
Context {uii : unique_indices_interface}.
Ltac log_matching_hosts_easy_case := repeat find_inversion; intros; eapply log_matching_hosts_ignores_packets; eauto; intros; simpl; repeat break_if; try congruence.
Ltac do_elim := match goal with | [ H : findAtIndex _ _ = Some _ |- _ ] => apply findAtIndex_elim in H; intuition | [ H : In _ (findGtIndex _ _) |- _ ] => apply findGtIndex_necessary in H; intuition end.
Ltac use_packet_subset_clear := match goal with | [ H : forall _, In _ _ -> _, H' : In _ _ |- _ ] => apply H in H'; clear H; intuition end.
Ltac use_packet_subset := match goal with | [ H : forall _, In _ _ -> _, H' : In _ _ |- _ ] => apply H in H'; intuition end.
Ltac use_nw_invariant := match goal with | [ H : forall _ _ _ _ _ _ _, In _ _ -> Net.pBody _ = _ -> _, H' : Net.pBody ?p = AppendEntries _ _ _ _ ?xs _, _ : In ?p (nwPackets _) |- _] => apply H in H'; clear H; intuition end.
Ltac rewrite_if_log := match goal with | [ H : _ |- _ ] => rewrite if_sum_bool_fun_comm with (f:=log) in * end.
Ltac use_log_matching_nw_host_keep := match goal with | [ H : forall _ _ _, In _ _ -> _, _ : eIndex ?e = eIndex ?e', Hin : In _ _ |- _ ] => match type of Hin with | context [ nwState _ ?h ] => let x := fresh in pose proof H as x; (specialize (H h e e'); do 4 concludes) || (specialize (H h e' e); do 4 concludes) end end.
Ltac use_log_matching_nw_host := match goal with | [ H : forall _ _ _, In _ _ -> _, _ : eIndex ?e = eIndex ?e', Hin : In _ _ |- _ ] => match type of Hin with | context [ nwState _ ?h ] => (specialize (H h e e'); do 4 concludes) || (specialize (H h e' e); do 4 concludes) end end.
Ltac solve_uniqueIndices := unfold uniqueIndices_host_invariant in *; intuition; match goal with | [ H : forall _, uniqueIndices _ |- _ ] => apply H end.
Ltac use_log_matching_nw_nw := match goal with | [ H : forall _ _ _ _ _ _ _, In _ _ -> _, Hp' : Net.pBody ?p' = AppendEntries _ _ _ _ ?entries' _, Hp : Net.pBody ?p = _ |- context [ In _ ?entries' ] ] => apply H in Hp; clear H; intuition | [ H : forall _ _ _ _ _ _ _, In _ _ -> _, Hp : Net.pBody _ = AppendEntries _ _ _ _ _ _, Hp' : Net.pBody _ = AppendEntries _ _ (eIndex ?e'') _ _ _ |- _ ] => apply H in Hp; auto; intuition; clear H | [ H : forall _ _ _ _ _ _ _, In _ _ -> _, Hp' : Net.pBody ?p' = AppendEntries _ _ _ ?plt' _ _, Hp : Net.pBody ?p = _ |- ?plt = ?plt' ] => apply H in Hp; auto; intuition; clear H end; try match goal with | [ H : forall _ _ _ _ _ _ _, In _ _ -> _, _ : eIndex ?e = eIndex ?e', Hp : Net.pBody ?p = _ |- _ ] => eapply H with (e1:=e)(e2:=e') in Hp; eauto end; intuition.
Ltac shouldSend_true := match goal with | _ : context [shouldSend ?st] |- _ => destruct (shouldSend st) eqn:? end; tuple_inversion; [|(solve [in_crush])].
Ltac do_doLeader_same_log := match goal with | [ H : doLeader _ _ = (_, ?d, _) |- _ ] => erewrite doLeader_same_log with (st':=d) in *; try apply H; eauto end.
Ltac do_tryToBecomeLeader_same_log := match goal with | [ H : tryToBecomeLeader _ _ = (?d, _) |- _ ] => erewrite tryToBecomeLeader_same_log with (st':=d); try apply H; eauto end.
Ltac do_state_same_packet_subset := repeat find_inversion; eapply log_matching_state_same_packet_subset; eauto; intros; simpl in *; try (try find_higher_order_rewrite; break_if; subst; auto); try (try find_apply_hyp_hyp; intuition).
Ltac assert_do_leader := match goal with | [ _ : nwPackets ?net = _, H : doLeader ?s ?h = (?out ?s' ?ms) |- _ ] => match goal with | [ |- log_matching {| nwPackets := map ?f (ms) ++ ?xs ++ ?ys; nwState := _ |} ] => assert (log_matching {| nwPackets := xs ++ ys; nwState := fun nm => if name_eq_dec nm h then s else nwState net nm |}) | [ |- log_matching {| nwPackets := ?p :: map ?f (ms) ++ ?xs ++ ?ys; nwState := _ |} ] => assert (log_matching {| nwPackets := p :: xs ++ ys; nwState := fun nm => if name_eq_dec nm h then s else nwState net nm |}) | [ |- log_matching {| nwPackets := map ?f (?l1 ++ ms) ++ ?xs ++ ?ys; nwState := _ |} ] => assert (log_matching {| nwPackets := map f l1 ++ xs ++ ys; nwState := fun nm => if name_eq_dec nm h then s else nwState net nm |}) | [ |- log_matching {| nwPackets := ?p ::map ?f (?l1 ++ ms) ++ ?xs ++ ?ys; nwState := _ |} ] => assert (log_matching {| nwPackets := p :: map f l1 ++ xs ++ ys; nwState := fun nm => if name_eq_dec nm h then s else nwState net nm |}) | [ |- log_matching {| nwPackets := map ?f (ms ++ ?l1) ++ ?xs ++ ?ys; nwState := _ |} ] => assert (log_matching {| nwPackets := map f l1 ++ xs ++ ys; nwState := fun nm => if name_eq_dec nm h then s else nwState net nm |}) | [ |- log_matching {| nwPackets := map ?f (?l1 ++ ?l2 ++ ms) ++ ?xs ++ ?ys; nwState := _ |} ] => assert (log_matching {| nwPackets := map f (l1 ++ l2) ++ xs ++ ys; nwState := fun nm => if name_eq_dec nm h then s else nwState net nm |}) | [ |- log_matching {| nwPackets := map ?f (?l1 ++ ms ++ ?l2) ++ ?xs ++ ?ys; nwState := _ |} ] => assert (log_matching {| nwPackets := map f (l1 ++ l2) ++ xs ++ ys; nwState := fun nm => if name_eq_dec nm h then s else nwState net nm |}) | [ |- log_matching {| nwPackets := map ?f (ms ++ ?l1 ++ ?l2) ++ ?xs ++ ?ys; nwState := _ |} ] => assert (log_matching {| nwPackets := map f (l1 ++ l2) ++ xs ++ ys; nwState := fun nm => if name_eq_dec nm h then s else nwState net nm |}) end end.
Ltac contradict_leader_sublog := match goal with | H : eIndex _ = S _ |- _ => exfalso; apply S_maxIndex_not_in in H; intuition; apply H; eauto | H : S _ = eIndex _ |- _ => symmetry in H; exfalso; apply S_maxIndex_not_in in H; intuition; apply H; eauto end.
Definition host_independent_log_matching_nw net := (forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit, In p (nwPackets net) -> pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> (forall i, prevLogIndex < i <= maxIndex entries -> exists e, eIndex e = i /\ In e entries) /\ (forall e, In e entries -> prevLogIndex < eIndex e) /\ (forall p' t' leaderId' prevLogIndex' prevLogTerm' entries' leaderCommit', In p' (nwPackets net) -> pBody p' = AppendEntries t' leaderId' prevLogIndex' prevLogTerm' entries' leaderCommit' -> (forall e1 e2, In e1 entries -> In e2 entries' -> eIndex e1 = eIndex e2 -> eTerm e1 = eTerm e2 -> (forall e3, prevLogIndex' < eIndex e3 <= eIndex e1 -> In e3 entries -> In e3 entries') /\ (forall e3, In e3 entries -> eIndex e3 = prevLogIndex' -> eTerm e3 = prevLogTerm') /\ (prevLogIndex <> 0 -> prevLogIndex = prevLogIndex' -> prevLogTerm = prevLogTerm')))).
Ltac do_host_independent := match goal with | [ H : log_matching_nw ?net |- log_matching_nw ?net2 ] => assert (host_independent_log_matching_nw net2); [apply (host_independent_log_matching_nw_invariant net); [ unfold host_independent_log_matching_nw; unfold log_matching_nw in H; apply H; simpl in *; intuition | simpl in *; repeat find_rewrite; intuition; try do_in_app; intuition ] |] end.
Ltac assert_do_generic_server h := match goal with | [ _ : nwPackets ?net = _, H : doGenericServer ?h ?s = (?out, ?s', ?ms) |- _ ] => match goal with | [ |- log_matching {| nwPackets := map ?f (?l1 ++ ms) ++ ?xs ++ ?ys; nwState := _ |} ] => assert (log_matching {| nwPackets := map f l1 ++ xs ++ ys; nwState := fun nm => if name_eq_dec nm h then s else nwState net nm |}) | [ |- log_matching {| nwPackets := map ?f (ms ++ ?l1) ++ ?xs ++ ?ys; nwState := _ |} ] => assert (log_matching {| nwPackets := map f l1 ++ xs ++ ys; nwState := fun nm => if name_eq_dec nm h then s else nwState net nm |}) end end.
Ltac use_entries_match := match goal with | [ _ : eIndex ?e1 = eIndex ?e2, H : context [entries_match] |- _ ] => first [ solve [eapply H with (e:=e2)(e':=e1); eauto; congruence] | solve [eapply H with (e:=e1)(e':=e2); eauto; congruence]] end.
Ltac contradict_maxIndex := match goal with | [ _ : S (maxIndex ?l) <= eIndex ?e, He : In ?e ?l |- _ ] => exfalso; apply maxIndex_is_max in He; intuition; omega end.
Ltac use_nw_invariant_keep := match goal with | [ H : forall _ _ _ _ _ _ _, In _ _ -> Net.pBody _ = _ -> _, H' : Net.pBody ?p = AppendEntries _ _ _ _ ?xs _ |- _ ] => copy_apply H H'; clear H; intuition end.
Ltac use_leader_sublog := match goal with | [ H : forall _ _ _ _ _ _ _ _ _, type _ = _ -> In _ _ -> Net.pBody _ = _ -> _, H' : Net.pBody ?p = AppendEntries _ _ _ _ ?xs _ |- _ ] => eapply H in H'; clear H; eauto; intuition end.
Ltac pbody_massage := match goal with | H : In ?p _ |- _ => match type of H with | context [ nwPackets _ ] => fail 1 | context [AppendEntries ?t ?lid ?pli ?plt ?e ?lc] => assert (Net.pBody p = AppendEntries t lid pli plt e lc) by reflexivity end end.
Ltac prove_in := match goal with | _ : nwPackets ?net = ?xs ++ ?p :: ?ys, p : packet |- _ => assert (In p (nwPackets net)) by (repeat find_rewrite; in_crush) end.
Ltac contradict_append_entries := match goal with | H : is_append_entries _ -> False |- _ => exfalso; apply H; repeat eexists; eauto; repeat find_rewrite; simpl in *; eauto end.
Ltac ensure_pbody p := try match goal with | _ : pBody p = AppendEntries _ _ _ _ _ _ |- _ => fail 1 | H : context [AppendEntries ?t ?lid ?pli ?plt ?e ?lc] |- _ => assert (pBody p = AppendEntries t lid pli plt e lc) by eauto end.
Ltac use_nw p := ensure_pbody p; match goal with | [ Hinv : forall _ _ _ _ _ _ _, In _ _ -> Net.pBody _ = _ -> _, H: Net.pBody p = _, net : network |- _ ] => let Hin := fresh "H" in cut (In p (nwPackets net)); [intros Hin; apply Hinv in H; clear Hinv; intuition|]; intuition end.
Ltac use_log_matching_nw_nw' := match goal with | [ H : forall _ _ _ _ _ _ _, In _ _ -> _, Hp' : Net.pBody ?p' = AppendEntries _ _ _ _ ?entries' _, Hp : Net.pBody ?p = _ |- context [ In _ ?entries' ] ] => apply H in Hp'; clear H; intuition end; try match goal with | [ H : forall _ _ _ _ _ _ _, In _ _ -> _, _ : eIndex ?e = eIndex ?e', Hp : Net.pBody ?p = _ |- context [In _ ?entries' ] ] => match (type of H) with | context [entries'] => try (eapply H with (e1:=e)(e2:=e') in Hp; eauto; [idtac]); eapply H with (e1:=e')(e2:=e) in Hp; eauto end end; intuition.
Ltac ensure_sorted := match goal with | _ : pBody _ = AppendEntries _ _ _ _ ?es _ |- _ => try match goal with | _ : sorted es |- _ => fail 2 end; assert (sorted es) by eauto end.
Ltac prep_packets := simpl in *; repeat find_higher_order_rewrite; prove_in; repeat (find_apply_hyp_hyp; intuition; [|contradict_append_entries]; match goal with | _ : nwPackets ?net = (?xs ++ ?p1 :: ?ys), H : In ?p2 (?xs ++ ?ys) |- _ => let Heq := fresh "H" in let p' := fresh "p" in remember p2 as p' eqn:Heq; clear Heq; assert (In p' (nwPackets net)) by (repeat find_rewrite; in_crush); clear H end); match goal with | _ : nwPackets ?net = (?xs ++ ?p1 :: ?ys) |- _ => replace (xs ++ p1 :: ys) with (nwPackets net) in *; subst end; repeat ensure_sorted.
Instance lmi : log_matching_interface.
Proof.
split.
auto using log_matching_invariant.
End LogMatchingProof.

Lemma handleClientRequest_log_matching_hosts_entries_match : forall h h' net client id c, h' <> h -> log_matching_hosts net -> leader_sublog_host_invariant net -> logs_sorted_host net -> type (nwState net h) = Leader -> entries_match ((mkEntry h client id (S (maxIndex (log (nwState net h)))) (currentTerm (nwState net h)) c) :: (log (nwState net h))) (log (nwState net h')).
Proof using.
unfold entries_match.
intros.
intuition.
-
simpl in *.
intuition.
+
unfold log_matching_hosts in *.
subst.
simpl in *.
contradict_leader_sublog.
+
subst.
simpl in *.
contradict_leader_sublog.
+
subst.
simpl in *.
contradict_maxIndex.
+
unfold log_matching_hosts in *.
intuition.
use_entries_match.
-
simpl in *.
intuition.
+
subst.
simpl in *.
contradict_leader_sublog.
+
unfold log_matching_hosts in *.
intuition.
right.
Admitted.

Lemma leader_sublog_weaken_host : forall net, leader_sublog_invariant net -> leader_sublog_host_invariant net.
Proof using.
unfold leader_sublog_invariant.
Admitted.

Lemma logs_sorted_weaken_host : forall net, logs_sorted net -> logs_sorted_host net.
Proof using.
unfold logs_sorted.
Admitted.

Lemma client_request_log_matching : raft_net_invariant_client_request log_matching.
Proof using lsi si.
unfold raft_net_invariant_client_request.
intros.
unfold handleClientRequest in *.
break_match; try solve [do_state_same_packet_subset].
find_inversion.
unfold log_matching in *.
intuition.
-
unfold log_matching_hosts.
simpl in *.
intuition; repeat find_higher_order_rewrite; repeat rewrite if_sum_bool_fun_comm; simpl in *.
+
repeat break_if.
*
auto using entries_match_refl.
*
subst.
find_copy_apply_lem_hyp leader_sublog_invariant_invariant.
find_copy_apply_lem_hyp logs_sorted_invariant.
auto using entries_match_sym, leader_sublog_weaken_host, logs_sorted_weaken_host, handleClientRequest_log_matching_hosts_entries_match.
*
subst.
find_copy_apply_lem_hyp leader_sublog_invariant_invariant.
find_copy_apply_lem_hyp logs_sorted_invariant.
auto using entries_match_sym, leader_sublog_weaken_host, logs_sorted_weaken_host, handleClientRequest_log_matching_hosts_entries_match.
*
unfold log_matching_hosts in *.
intuition.
+
break_if; subst; simpl in *.
*
find_apply_lem_hyp le_lt_eq_dec.
intuition; [|eexists; intuition eauto]; simpl; auto.
unfold log_matching_hosts in *.
intuition.
assert (i <= maxIndex (log (nwState net h))) by omega.
cut (exists e : entry, eIndex e = i /\ In e (log (nwState net h))); [intros; break_exists; eexists; intuition eauto|].
eauto.
*
unfold log_matching_hosts in *.
intuition.
+
unfold log_matching_hosts in *.
break_if; simpl in *; try do_in_app; simpl in *; intuition eauto; subst; simpl; auto with *.
-
unfold log_matching_nw.
intuition; simpl in *; repeat find_higher_order_rewrite; repeat rewrite if_sum_bool_fun_comm in *; simpl in *.
+
break_if; subst.
*
{
intuition.
-
subst.
simpl in *.
find_copy_apply_lem_hyp leader_sublog_invariant_invariant.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold leader_sublog_invariant, leader_sublog_nw_invariant, logs_sorted in *.
intuition.
contradict_leader_sublog.
unfold log_matching_nw in *.
use_leader_sublog.
find_apply_hyp_hyp.
intuition.
-
right.
unfold log_matching_nw in *.
intuition.
find_apply_hyp_hyp.
intuition.
use_nw_invariant.
use_log_matching_nw_host.
intuition.
}
*
unfold log_matching_nw in *.
find_apply_hyp_hyp.
intuition.
use_nw_invariant.
use_log_matching_nw_host.
intuition.
+
break_if; subst.
*
{
intuition.
-
subst.
simpl in *.
find_copy_apply_lem_hyp leader_sublog_invariant_invariant.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold leader_sublog_invariant, leader_sublog_nw_invariant, logs_sorted in *.
intuition.
contradict_leader_sublog.
unfold log_matching_nw in *.
use_leader_sublog.
find_apply_hyp_hyp.
intuition.
-
simpl.
unfold log_matching_nw in *.
intuition.
find_apply_hyp_hyp.
intuition.
use_nw_invariant.
use_log_matching_nw_host.
intuition.
break_exists; eexists; intuition eauto.
}
*
unfold log_matching_nw in *.
find_apply_hyp_hyp.
intuition.
use_nw_invariant.
use_log_matching_nw_host.
intuition.
+
unfold log_matching_nw in *.
find_apply_hyp_hyp.
intuition.
use_nw_invariant.
+
unfold log_matching_nw in *.
find_apply_hyp_hyp.
intuition.
use_nw_invariant.
+
unfold log_matching_nw in *.
do 2 (find_apply_hyp_hyp; intuition).
subst.
use_log_matching_nw_nw.
+
unfold log_matching_nw in *.
do 2 (find_apply_hyp_hyp; intuition).
subst.
use_log_matching_nw_nw.
+
unfold log_matching_nw in *.
do 2 (find_apply_hyp_hyp; intuition).
subst.
Admitted.

Lemma tryToBecomeLeader_spec : forall h d out d' l, tryToBecomeLeader h d = (out, d', l) -> log d' = log d /\ (forall m, In m l -> ~ is_append_entries (snd m)).
Proof using.
intuition eauto using tryToBecomeLeader_same_log.
unfold tryToBecomeLeader in *.
find_inversion.
do_in_map.
subst.
simpl in *.
Admitted.

Lemma handleTimeout_log_matching : raft_net_invariant_timeout log_matching.
Proof using.
unfold raft_net_invariant_timeout.
intros.
unfold handleTimeout in *.
break_match; try solve [ find_apply_lem_hyp tryToBecomeLeader_spec; eauto; do_state_same_packet_subset; do_in_map; subst; simpl in *; exfalso; find_apply_hyp_hyp; repeat eexists; eauto ].
do_state_same_packet_subset.
repeat find_higher_order_rewrite.
Admitted.

Lemma handleRequestVote_doesn't_send_AE : forall h st t n lli llt d m, handleRequestVote h st t n lli llt = (d, m) -> ~ is_append_entries m.
Proof using.
intros.
unfold handleRequestVote in *.
Admitted.

Lemma handleRequestVote_log_matching : raft_net_invariant_request_vote log_matching.
Proof using.
unfold raft_net_invariant_request_vote.
intros.
do_state_same_packet_subset.
-
find_apply_lem_hyp handleRequestVote_same_log.
auto.
-
find_rewrite.
eauto.
-
exfalso.
find_apply_lem_hyp handleRequestVote_doesn't_send_AE.
subst.
simpl in *.
Admitted.

Lemma handleRequestVoteReply_log_matching : raft_net_invariant_request_vote_reply log_matching.
Proof using.
unfold raft_net_invariant_request_vote_reply.
intros.
do_state_same_packet_subset.
rewrite handleRequestVoteReply_same_log.
Admitted.

Lemma log_matching_init : raft_net_invariant_init log_matching.
Proof using.
unfold raft_net_invariant_init, log_matching, log_matching_hosts, log_matching_nw.
Admitted.

Lemma handleAppendEntriesReply_doesn't_send_AE : forall n st src t es b st' l, handleAppendEntriesReply n st src t es b = (st', l) -> forall x, In x l -> ~ is_append_entries (snd x).
Proof using.
intros.
unfold handleAppendEntriesReply in *.
Admitted.

Lemma handleAppendEntriesReply_log_matching : raft_net_invariant_append_entries_reply log_matching.
Proof using.
unfold raft_net_invariant_append_entries_reply.
intros.
do_state_same_packet_subset; eauto.
-
find_apply_lem_hyp handleAppendEntriesReply_same_log.
auto.
-
exfalso.
do_in_map.
find_eapply_lem_hyp handleAppendEntriesReply_doesn't_send_AE; eauto.
subst; simpl in *.
find_rewrite.
match goal with | H : ~ _ |- _ => apply H end.
Admitted.

Lemma handleAppendEntries_log_matching_beginning_of_time_entries_match : forall net p t n plt es ci h, log_matching_hosts net -> log_matching_nw net -> logs_sorted_nw net -> uniqueIndices_host_invariant net -> In p (nwPackets net) -> pBody p = AppendEntries t n 0 plt es ci -> pDst p <> h -> entries_match es (log (nwState net h)).
Proof using.
intros.
unfold log_matching_nw in *.
use_nw_invariant_keep.
eapply entries_match_scratch; eauto; intuition.
unfold log_matching_hosts in *.
Admitted.

Lemma handleAppendEntries_spec : forall h d t from pli plt entries lci d' m, handleAppendEntries h d t from pli plt entries lci = (d', m) -> ~ is_append_entries m /\ (log d' = log d \/ (pli = 0 /\ log d' = entries) \/ (pli <> 0 /\ (exists e, findAtIndex (log d) pli = Some e /\ eTerm e = plt) /\ log d' = entries ++ (removeAfterIndex (log d) pli))).
Proof using.
intros.
unfold handleAppendEntries in *.
repeat (break_match; try find_inversion; intuition; simpl in *; do_bool; subst; intuition; break_exists; try congruence; eauto using advanceCurrentTerm_log).
right.
right.
intuition.
Admitted.

Lemma handleAppendEntries_log_matching_middle_of_time_entries_match : forall net p t n pli plt es ci h ple, log_matching_hosts net -> log_matching_nw net -> logs_sorted_host net -> logs_sorted_nw net -> uniqueIndices_host_invariant net -> In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> findAtIndex (log (nwState net (pDst p))) pli = Some ple -> eTerm ple = plt -> pli <> 0 -> entries_match (es ++ (removeAfterIndex (log (nwState net (pDst p))) pli)) (log (nwState net h)).
Proof using.
intros.
eapply entries_match_append; eauto; try solve [intros; eapply_prop log_matching_nw; eauto].
Admitted.

Lemma contiguous_range_exact_lo_weaken_exists : forall es lo i, contiguous_range_exact_lo es lo -> lo < i <= maxIndex es -> exists e, eIndex e = i /\ In e es.
Proof using.
unfold contiguous_range_exact_lo.
intros.
Admitted.

Lemma handleAppendEntries_log_matching : raft_net_invariant_append_entries log_matching.
Proof using uii si.
unfold raft_net_invariant_append_entries.
intros.
find_copy_apply_lem_hyp UniqueIndices_invariant.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted, UniqueIndices in *.
intuition.
find_eapply_lem_hyp handleAppendEntries_spec.
intuition.
-
eapply log_matching_state_same_packet_subset; eauto.
+
intros.
find_higher_order_rewrite.
simpl.
break_if; subst; intuition.
+
in_crush.
find_apply_hyp_hyp.
intuition; find_rewrite; in_crush.
-
unfold log_matching in *.
intuition.
+
unfold log_matching_hosts.
simpl in *.
subst.
{
intuition.
-
repeat find_higher_order_rewrite.
simpl.
repeat break_if; subst; simpl in *; auto using entries_match_refl; eauto using entries_match_sym, handleAppendEntries_log_matching_beginning_of_time_entries_match.
find_apply_hyp_goal.
-
repeat find_higher_order_rewrite.
simpl in *.
break_if.
+
unfold log_matching_nw in *.
repeat subst.
prove_in.
use_nw_invariant.
+
unfold log_matching_hosts in *.
intuition.
-
repeat find_higher_order_rewrite.
simpl in *.
break_if.
+
unfold log_matching_nw in *.
repeat find_rewrite.
prove_in.
use_nw_invariant.
+
unfold log_matching_hosts in *.
intuition eauto.
}
+
unfold log_matching_nw in *.
{
intuition; prep_packets.
-
break_if.
+
use_log_matching_nw_nw.
match goal with | [ H : forall _, _ < _ <= _ -> In _ _ -> In _ ?es |- In _ ?es ] => eapply H; eauto; split end.
match goal with | [ H : forall _, In _ ?es -> _ < eIndex _, _ : In ?e ?es |- 0 < eIndex ?e ] => eapply le_lt_trans; [omega|eapply H; eauto] end.
congruence.
+
use_nw_invariant; try solve [in_crush].
use_log_matching_nw_host.
intuition.
-
break_if.
+
subst.
match goal with | [ H : forall _ _ _ _ _ _ _, In _ _ -> _, Hp : pBody _ = _ |- context [In _ ?es] ] => match type of Hp with | context [ es ] => fail 1 | _ => copy_apply H Hp; eauto end end.
use_log_matching_nw_nw'.
intuition.
match goal with | H : forall _, 0 < _ <= _ -> _ |- context [eIndex _ = ?x] => specialize (H x); forward H end.
*
split; [destruct prevLogIndex; [congruence|omega]|].
apply lt_le_weak.
eapply lt_le_trans.
eauto.
repeat find_rewrite.
eapply maxIndex_is_max; intuition eauto.
*
concludes.
break_exists.
intuition.
eauto.
+
use_nw_invariant.
use_log_matching_nw_host.
intuition.
-
use_nw_invariant.
-
use_nw_invariant.
-
match goal with | H : pBody _ = AppendEntries _ _ _ _ (log _) _ |- _ => clear H end.
use_log_matching_nw_nw.
-
match goal with | H : pBody _ = AppendEntries _ _ _ _ (log _) _ |- _ => clear H end.
use_log_matching_nw_nw.
-
match goal with | H : pBody _ = AppendEntries _ _ _ _ (log _) _ |- _ => clear H end.
use_log_matching_nw_nw.
}
-
simpl in *.
unfold log_matching in *.
intuition.
+
{
unfold log_matching_hosts.
intuition.
-
simpl in *.
repeat find_higher_order_rewrite.
repeat break_if; subst; eauto using entries_match_refl.
+
find_rewrite.
break_exists; intuition.
eapply handleAppendEntries_log_matching_middle_of_time_entries_match; eauto.
+
find_rewrite.
break_exists; intuition.
apply entries_match_sym.
eapply handleAppendEntries_log_matching_middle_of_time_entries_match; eauto.
+
unfold log_matching_hosts in *.
intuition.
-
simpl in *.
repeat find_higher_order_rewrite.
break_if; subst.
+
apply contiguous_range_exact_lo_weaken_exists with (lo := 0); [|omega].
break_exists.
intuition.
do_elim.
repeat find_rewrite.
eapply removeIncorrect_new_contiguous; eauto.
*
intros.
unfold log_matching_nw in *.
prove_in.
use_nw_invariant.
use_log_matching_nw_host.
intuition.
eapply uniqueIndices_elim_eq; eauto.
*
unfold contiguous_range_exact_lo.
unfold log_matching_hosts in *.
intuition eauto.
find_apply_hyp_hyp.
intuition.
*
unfold contiguous_range_exact_lo.
unfold log_matching_nw in *.
prove_in.
use_nw_invariant.
+
unfold log_matching_hosts in *.
intuition.
-
simpl in *.
repeat find_higher_order_rewrite.
break_if; subst.
+
repeat find_rewrite.
do_in_app.
intuition.
*
unfold log_matching_nw in *.
prove_in.
use_nw_invariant.
find_apply_hyp_hyp.
intuition.
*
find_apply_lem_hyp removeAfterIndex_in.
unfold log_matching_hosts in *.
intuition eauto.
+
unfold log_matching_hosts in *.
intuition eauto.
}
+
{
unfold log_matching_nw.
intuition; prep_packets.
-
break_if; subst.
+
repeat find_rewrite.
in_crush_start.
*
{
match goal with | |- In ?e (_ ++ removeAfterIndex _ ?i) => destruct (le_lt_dec (eIndex e) i) end.
-
unfold log_matching_nw in *.
repeat find_rewrite.
match goal with | [ Hp : pBody ?p = AppendEntries _ _ _ _ ?es _, Hp' : pBody ?p' = AppendEntries _ _ _ _ ?entries _, H : forall _ _ _ _ _ _ _, In _ _ -> _ |- context [ ?es ++ _ ] ]=> copy_apply H Hp'; [|in_crush]; copy_apply H Hp; [|in_crush]; clear H; intuition; match goal with | [ H : forall _ _ _ _ _ _ _, In _ _ -> _, H' : forall _ _ _ _ _ _ _, In _ _ -> _, _ : eIndex ?e = eIndex ?e' |- _] => match type of H with | context [ ?es ] => match type of H' with | context [ ?entries ] => eapply H with (e1:=e)(e2:=e') in Hp; eauto; eapply H' with (e1:=e')(e2:=e) in Hp'; eauto; intuition; clear H; clear H' end end end end.
repeat do_elim.
match goal with | [ H : forall _, prevLogIndex < _ <= _ -> _ |- context [removeAfterIndex _ ?pli ] ] => specialize (H pli); forward H end.
+
split; [solve [eauto using lt_le_trans]|].
eapply lt_le_weak.
eapply lt_le_trans; eauto.
repeat find_reverse_rewrite.
eapply maxIndex_is_max; eauto.
+
concludes.
break_exists; intuition.
apply in_or_app.
right.
{
eapply removeAfterIndex_le_In.
-
omega.
-
do_elim.
subst.
match goal with | [ H : forall _ _ _, In _ ?entries -> _, _ : eIndex ?e3 <= eIndex _, _ : In ?e3 ?entries, _ : In ?e (log _), _ : eIndex ?x = eIndex ?e |- _ ] => eapply H with (e1:=x)(e2:=e); auto; congruence end.
}
-
apply in_or_app.
left.
unfold log_matching_nw in *.
use_log_matching_nw_nw.
}
*
apply in_or_app.
right.
unfold log_matching_nw in *.
use_nw_invariant.
find_copy_apply_lem_hyp removeAfterIndex_In_le.
find_apply_lem_hyp removeAfterIndex_in.
apply removeAfterIndex_le_In; [omega|].
use_log_matching_nw_host.
intuition.
eapply_prop logs_sorted_host.
+
unfold log_matching_nw in *.
use_nw_invariant.
use_log_matching_nw_host.
intuition.
-
simpl in *.
{
break_if.
-
subst.
repeat find_rewrite.
match goal with | [ _ : eIndex _ = eIndex ?e', H : In ?e' (_ ++ _) |- _ ] => apply in_app_or in H; intuition end.
+
unfold log_matching_nw in *.
repeat find_rewrite.
match goal with | [ Hp : pBody ?p = AppendEntries _ _ _ _ ?es _, Hp' : pBody ?p' = AppendEntries _ _ _ _ ?entries _, H : forall _ _ _ _ _ _ _, In _ _ -> _ |- context [ ?es ++ _ ] ]=> copy_apply H Hp'; [|in_crush]; copy_apply H Hp; [|in_crush]; clear H; intuition; match goal with | [ H : forall _ _ _ _ _ _ _, In _ _ -> _, H' : forall _ _ _ _ _ _ _, In _ _ -> _, _ : eIndex ?e = eIndex ?e' |- _] => match type of H with | context [ ?es ] => match type of H' with | context [ ?entries ] => eapply H with (e1:=e)(e2:=e') in Hp; eauto; eapply H' with (e1:=e')(e2:=e) in Hp'; eauto; intuition; clear H; clear H' end end end end.
destruct (lt_eq_lt_dec prevLogIndex pli); intuition.
*
match goal with | [ H : forall _, prevLogIndex < _ <= _ -> _ |- _ ] => specialize (H pli); conclude H ltac:( split; intuition; eapply lt_le_weak; eapply lt_le_trans; eauto; repeat find_reverse_rewrite; apply maxIndex_is_max; eauto) end.
break_exists; intuition.
do_elim.
subst.
match goal with | [ H : forall _, In _ entries -> _ |- _ ] => specialize (H x); repeat concludes end.
subst.
use_log_matching_nw_host.
intuition.
break_exists.
repeat find_rewrite.
exists x1.
intuition.
apply in_or_app.
right.
apply removeAfterIndex_le_In; intuition.
*
subst.
break_exists.
intuition.
do_elim.
eexists; intuition eauto.
apply in_or_app.
right.
apply removeAfterIndex_le_In; intuition.
*
match goal with | [ H : forall _, pli < _ <= _ -> _ |- _ ] => specialize (H prevLogIndex); conclude H ltac:( split; auto; eapply lt_le_weak; eapply lt_le_trans; [eauto | repeat find_rewrite; eapply maxIndex_is_max; eauto]) end.
break_exists.
exists x.
intuition.
+
unfold log_matching_nw in *.
repeat find_rewrite.
use_nw_invariant.
find_copy_apply_lem_hyp removeAfterIndex_in.
find_apply_lem_hyp removeAfterIndex_In_le; intuition.
use_log_matching_nw_host.
intuition.
break_exists.
intuition.
subst.
exists x.
intuition.
apply in_or_app.
right.
apply removeAfterIndex_le_In; eauto.
apply lt_le_weak.
eapply lt_le_trans; eauto.
repeat find_rewrite.
eauto.
-
unfold log_matching_nw in *.
repeat find_rewrite.
use_nw_invariant.
use_log_matching_nw_host.
intuition.
}
-
simpl in *.
unfold log_matching_nw in *.
repeat find_rewrite.
use_nw_invariant.
-
simpl in *.
unfold log_matching_nw in *.
repeat find_rewrite.
use_nw_invariant.
-
simpl in *.
unfold log_matching_nw in *.
repeat find_rewrite.
use_log_matching_nw_nw.
-
simpl in *.
unfold log_matching_nw in *.
repeat find_rewrite.
use_log_matching_nw_nw.
-
simpl in *.
unfold log_matching_nw in *.
repeat find_rewrite.
use_log_matching_nw_nw.
Admitted.

Theorem log_matching_invariant: forall net, raft_intermediate_reachable net -> log_matching net.
Proof using uii lsi si.
intros.
apply raft_net_invariant; eauto.
-
exact log_matching_init.
-
exact client_request_log_matching.
-
exact handleTimeout_log_matching.
-
exact handleAppendEntries_log_matching.
-
exact handleAppendEntriesReply_log_matching.
-
exact handleRequestVote_log_matching.
-
exact handleRequestVoteReply_log_matching.
-
exact do_leader_log_matching.
-
exact doGenericServer_log_matching.
-
unfold raft_net_invariant_state_same_packet_subset.
intros.
eapply log_matching_state_same_packet_subset; eauto.
intros.
find_higher_order_rewrite.
auto.
-
Admitted.

Instance lmi : log_matching_interface.
Proof.
split.
Admitted.

Lemma log_matching_reboot : raft_net_invariant_reboot log_matching.
Proof using.
unfold raft_net_invariant_reboot.
intros.
unfold reboot in *.
subst.
simpl in *.
eapply log_matching_state_same_packet_subset; eauto; intros; repeat find_higher_order_rewrite; try break_if; subst; simpl in *; auto.

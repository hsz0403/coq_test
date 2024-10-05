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

Lemma log_matching_hosts_ignores_packets : forall net net', log_matching_hosts net -> (forall h, log (nwState net h) = log (nwState net' h)) -> log_matching_hosts net'.
Proof using.
intros.
unfold log_matching_hosts in *.
Admitted.

Lemma log_matching_state_same_packet_subset : forall net net', log_matching net -> (forall h, log (nwState net h) = log (nwState net' h)) -> (forall p, is_append_entries (pBody p) -> In p (nwPackets net') -> In p (nwPackets net)) -> log_matching net'.
Proof using.
intros.
split; unfold log_matching in *.
-
intuition.
eauto using log_matching_hosts_ignores_packets.
-
unfold log_matching_nw in *.
intros.
match goal with | [ H : forall _, is_append_entries _ -> _, H' : In ?p (nwPackets _) |- _] => pose proof H as Hpkt; specialize (H p); forward H; [solve [repeat eexists; eauto]|]; conclude H auto; repeat concludes end.
break_and.
match goal with | [ H : forall _ _ _ _, _, H' : pBody ?p = _, H'' : In ?p _ |- _ ] => specialize (H _ _ _ _ _ _ _ H'' H') end.
Admitted.

Theorem doLeader_log_matching_nw : forall net h out d ms net', doLeader (nwState net h) h = (out, d, ms) -> logs_sorted net -> log_matching net -> uniqueIndices_host_invariant net -> (forall p, In p (nwPackets net') -> In p (nwPackets net) \/ In p (map (fun m => mkPacket h (fst m) (snd m)) ms)) -> (forall h', nwState net' h' = if name_eq_dec h' h then d else nwState net h') -> log_matching_nw net'.
Proof using.
intros.
find_copy_apply_lem_hyp doLeader_same_log.
unfold doLeader in *.
break_match; repeat break_let; repeat tuple_inversion; simpl in *; try solve [ eapply log_matching_state_same_packet_subset; eauto; intros; try use_packet_subset_clear; match goal with | [ H : _ |- _ ] => rewrite H; solve [break_if; subst; auto] end].
unfold log_matching_nw.
intuition.
-
repeat find_higher_order_rewrite.
rewrite if_sum_bool_fun_comm in *.
repeat find_rewrite.
match goal with H : log _ = log _ |- _ => clear H end.
unfold log_matching in *.
intuition.
use_packet_subset_clear.
+
unfold log_matching_nw in *.
intuition.
use_nw_invariant.
break_if; match goal with | [ _ : eIndex ?e = eIndex ?e', H : forall _ _ _, In _ _ -> _ |- context [(?h : name) ] ] => specialize (H h e e') end; repeat concludes; intuition.
+
simpl in *.
shouldSend_true.
unfold log_matching_hosts in *.
repeat do_in_map.
find_inversion.
unfold replicaMessage in *.
subst.
simpl in *.
find_inversion.
break_if; repeat do_elim; repeat find_rewrite.
match goal with | [ H : forall _ _, entries_match _ _, _ : eIndex ?e1 = eIndex ?e2 |- _ ] => eapply H with (e':=e1)(e:=e2); eauto end.
-
repeat find_higher_order_rewrite.
rewrite if_sum_bool_fun_comm in *.
repeat find_rewrite.
match goal with H : log _ = log _ |- _ => clear H end.
unfold log_matching in *.
intuition.
use_packet_subset_clear.
+
unfold log_matching_nw in *.
use_nw_invariant.
simpl in *.
break_if; subst; use_log_matching_nw_host; repeat concludes; intuition.
+
shouldSend_true.
repeat do_in_map.
subst.
simpl in *.
do 2 find_inversion.
simpl.
unfold log_matching_hosts in *.
intuition.
rewrite <- if_sum_bool_fun_comm with (f:= log) in *.
rewrite <- if_sum_bool_fun_comm with (f:= nwState net) in *.
do_elim.
simpl in *.
unfold getNextIndex in *.
simpl in *.
match goal with | [ H : forall _ _, 1 <= _ <= _ -> _ |- context [eIndex _ = ?x] ] => remember (x) as index; specialize (H leaderId index); forward H end.
*
intuition; try (destruct index; intuition; omega).
match goal with | _ : eIndex ?e > index, _ : In ?e ?l |- _ => pose proof maxIndex_is_max l e end.
unfold logs_sorted in *.
intuition.
match goal with | H : logs_sorted_host _ |- _ => specialize (H leaderId) end.
repeat concludes.
omega.
*
{
concludes.
break_exists.
intuition.
eexists; intuition eauto.
-
break_match.
+
f_equal.
eapply findAtIndex_uniq_equal; eauto.
repeat find_rewrite; auto.
+
exfalso.
eapply findAtIndex_None; eauto.
unfold logs_sorted in *.
intuition.
-
break_if; auto.
unfold entries_match in *.
subst.
match goal with | [Hentries : forall _ _ _ _ _, eIndex _ = eIndex _ -> _, _ : eIndex ?e1 = eIndex ?e2, _ : In ?x (log (_ _ ?leader)) |- In ?x (log (_ _ ?h)) ] => specialize (Hentries leader h e1 e2 x) end.
assert (eIndex x <= eIndex e1) by omega.
repeat conclude.
intuition.
}
-
use_packet_subset_clear; unfold log_matching in *; intuition.
+
unfold log_matching_nw in *; intuition.
use_nw_invariant.
+
shouldSend_true.
repeat do_in_map.
subst.
simpl in *.
find_inversion.
unfold log_matching_hosts in *; intuition.
find_inversion.
match goal with | [ H : forall _ _, _ <= _ <= _ -> _, H' : ?i <= maxIndex _ |- _ ] => match type of H' with | context [ nwState _ ?h ] => specialize (H h i) end; conclude H ltac:(split; try omega; eapply le_trans; eauto using findGtIndex_max) end.
break_exists; eexists; intuition; eauto; eauto using findGtIndex_sufficient.
unfold logs_sorted in *.
apply findGtIndex_sufficient; intuition.
-
use_packet_subset_clear.
+
unfold log_matching, log_matching_nw in *; intuition.
use_nw_invariant.
+
shouldSend_true.
simpl in *.
clean.
repeat do_in_map.
subst.
simpl in *.
find_inversion.
do_elim.
-
use_packet_subset; use_packet_subset_clear.
+
unfold log_matching, log_matching_nw in *; intuition.
use_log_matching_nw_nw.
+
shouldSend_true.
unfold log_matching, log_matching_nw in *.
intuition.
unfold logs_sorted in *.
intuition.
match goal with | |- In _ ?es => assert (sorted entries') by eauto end.
use_nw_invariant.
simpl in *.
clean.
repeat do_in_map.
simpl in *.
do 2 (find_inversion; simpl in *).
repeat do_elim.
use_log_matching_nw_host_keep; repeat concludes; intuition.
match goal with | [ H : forall _, _ < _ <= _ -> _, _ : eIndex ?e3 <= eIndex _ |- _ ] => specialize (H (eIndex e3)); conclude H ltac:(split; auto; repeat find_rewrite; eapply le_trans; eauto; apply maxIndex_is_max; intuition) end.
break_exists.
intuition.
match goal with | [ _ : In ?x _, _ : eIndex ?x = eIndex ?e3, _ : eIndex ?e3 <= eIndex _ |- _ ] => eapply rachet with (x' := x); eauto end.
match goal with | H : forall _, eIndex _ <= eIndex _ -> _ |- _ => apply H; eauto; omega end.
+
shouldSend_true.
unfold log_matching, log_matching_nw in *.
intuition.
use_nw_invariant.
simpl in *.
clean.
repeat do_in_map.
simpl in *.
do 2 (find_inversion; simpl in *).
repeat do_elim.
use_log_matching_nw_host; repeat concludes; intuition.
unfold logs_sorted in *.
apply findGtIndex_sufficient; intuition eauto.
+
shouldSend_true.
simpl in *.
clean.
repeat do_in_map.
do 3 (find_inversion; simpl in *).
repeat do_elim.
unfold logs_sorted in *.
apply findGtIndex_sufficient; intuition eauto.
-
use_packet_subset; use_packet_subset_clear.
+
unfold log_matching, log_matching_nw in *; intuition.
use_log_matching_nw_nw.
+
shouldSend_true.
unfold log_matching, log_matching_nw in *.
intuition.
use_nw_invariant.
simpl in *.
clean.
repeat do_in_map.
simpl in *.
do 2 (find_inversion; simpl in *).
repeat do_elim.
use_log_matching_nw_host; repeat concludes; intuition.
break_exists.
intuition.
match goal with | _ : eIndex ?x = eIndex ?y |- context [ ?y ] => cut (x = y); [intros; subst; intuition|] end.
eapply uniqueIndices_elim_eq; eauto.
+
shouldSend_true.
unfold log_matching, log_matching_nw in *.
intuition.
use_nw_invariant.
simpl in *.
clean.
repeat do_in_map.
simpl in *.
do 2 (find_inversion; simpl in *).
break_match.
*
repeat do_elim.
find_rewrite.
use_log_matching_nw_host.
intuition.
match goal with | H : forall _, _ -> In _ ?es -> In _ ?es' |- eTerm ?e = eTerm ?e' => assert (In e es') by (apply H; auto; omega) end.
match goal with | _ : eIndex ?x = eIndex ?y |- context [ ?y ] => cut (x = y); [intros; subst; intuition|] end.
eapply uniqueIndices_elim_eq; eauto.
*
exfalso.
repeat do_elim.
unfold log_matching_hosts in *.
intuition.
repeat find_rewrite.
match goal with | _ : findAtIndex (log (nwState _ ?h)) ?i = None, H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h i) end.
intuition.
forwards; [match goal with | H : forall _, In _ _ -> _ < _ |- context [ (?e : entry) ] => specialize (H e) end; concludes; omega|].
concludes.
unfold logs_sorted in *.
forwards; [find_apply_lem_hyp maxIndex_is_max; intuition; omega|].
concludes.
break_exists.
intuition.
eapply findAtIndex_None; intuition eauto.
+
shouldSend_true.
simpl in *.
clean.
repeat do_in_map.
simpl in *.
do 3 (find_inversion; simpl in *).
repeat do_elim.
repeat find_rewrite.
unfold logs_sorted in *.
match goal with [ |- context [findAtIndex ?l (eIndex ?e) ] ] => assert (findAtIndex l (eIndex e) = Some e); (intuition eauto using findAtIndex_intro) end.
break_match; congruence.
-
use_packet_subset; use_packet_subset_clear.
+
unfold log_matching, log_matching_nw in *; intuition.
use_log_matching_nw_nw.
+
shouldSend_true.
unfold log_matching, log_matching_nw in *.
intuition.
use_nw_invariant.
repeat do_in_map.
do 3 (find_inversion; simpl in *).
repeat do_elim.
use_log_matching_nw_host.
intuition.
break_exists.
unfold logs_sorted in *.
intuition.
repeat find_reverse_rewrite.
match goal with [ |- context [findAtIndex ?l (eIndex ?e) ] ] => assert (findAtIndex l (eIndex e) = Some e) by (intuition eauto using findAtIndex_intro) end.
repeat break_match; congruence.
+
shouldSend_true.
unfold log_matching, log_matching_nw in *.
intuition.
use_nw_invariant.
repeat do_in_map.
do 3 (find_inversion; simpl in *).
repeat do_elim.
use_log_matching_nw_host.
intuition.
break_exists.
intuition.
repeat find_reverse_rewrite.
unfold logs_sorted in *.
match goal with [ |- context [findAtIndex ?l (eIndex ?e) ] ] => assert (findAtIndex l (eIndex e) = Some e) by (intuition eauto using findAtIndex_intro) end.
repeat break_match; congruence.
+
shouldSend_true.
simpl in *.
clean.
repeat do_in_map.
simpl in *.
do 3 (find_inversion; simpl in *).
Admitted.

Lemma doLeader_doesn't_touch_log : forall d h out d' ms, doLeader d h = (out, d', ms) -> log d' = log d.
Proof using.
intros.
unfold doLeader in *.
Admitted.

Lemma do_leader_log_matching : raft_net_invariant_do_leader log_matching.
Proof using uii si.
unfold raft_net_invariant_do_leader, log_matching.
intuition.
-
find_apply_lem_hyp doLeader_doesn't_touch_log.
unfold log_matching_hosts in *; simpl in *.
match goal with H : nwState _ _ = _ |- _ => symmetry in H end.
intuition; repeat find_higher_order_rewrite; repeat break_if; repeat find_rewrite; simpl in *; eauto.
-
find_reverse_rewrite.
eapply doLeader_log_matching_nw; eauto.
+
eauto using logs_sorted_invariant.
+
unfold log_matching.
auto.
+
Admitted.

Lemma host_independent_log_matching_nw_invariant : forall net net', host_independent_log_matching_nw net -> (forall p, is_append_entries (pBody p) -> In p (nwPackets net') -> In p (nwPackets net)) -> host_independent_log_matching_nw net'.
Proof using.
Admitted.

Theorem doGenericServer_log_matching : raft_net_invariant_do_generic_server log_matching.
Proof using.
unfold raft_net_invariant_do_generic_server.
intros.
subst.
unfold doGenericServer in *.
break_let.
repeat find_inversion; eapply log_matching_state_same_packet_subset; eauto; intros; use_applyEntries_spec; subst; simpl in *.
-
find_higher_order_rewrite.
rewrite if_sum_bool_fun_comm.
simpl.
break_if; subst; auto.
-
find_apply_hyp_hyp.
Admitted.

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

Lemma log_matching_reboot : raft_net_invariant_reboot log_matching.
Proof using.
unfold raft_net_invariant_reboot.
intros.
unfold reboot in *.
subst.
simpl in *.
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

Theorem handleAppendEntries_entries_in : forall h s t n prevT prevI entries c d m e, handleAppendEntries h s t n prevT prevI entries c = (d, m) -> In e (log d) -> (In e (log s) \/ In e entries).
Proof using.
intros.
unfold handleAppendEntries in *.
repeat break_match; find_inversion; simpl in *; intuition; repeat find_rewrite_lem advanceCurrentTerm_log; intuition.
simpl in *.
do_in_app.
intuition.
eauto using removeAfterIndex_in.

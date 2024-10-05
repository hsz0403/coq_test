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

Lemma handleAppendEntries_log_matching_beginning_of_time_entries_match : forall net p t n plt es ci h, log_matching_hosts net -> log_matching_nw net -> logs_sorted_nw net -> uniqueIndices_host_invariant net -> In p (nwPackets net) -> pBody p = AppendEntries t n 0 plt es ci -> pDst p <> h -> entries_match es (log (nwState net h)).
Proof using.
intros.
unfold log_matching_nw in *.
use_nw_invariant_keep.
eapply entries_match_scratch; eauto; intuition.
unfold log_matching_hosts in *.
match goal with | [ H : _ |- _ ] => solve [eapply H; eauto] end.

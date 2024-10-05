Require Import Verdi.Verdi.
Require Import Verdi.DynamicNetLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import FunctionalExtensionality.
Require Import Sorting.Permutation.
Require Import Sumbool.
Require Import Verdi.Ssrexport.
Set Implicit Arguments.
Class BaseParamsTotalMap (P0 : BaseParams) (P1 : BaseParams) := { tot_map_data : @data P0 -> @data P1 ; tot_map_input : @input P0 -> @input P1 ; tot_map_output : @output P0 -> @output P1 }.
Class MultiParamsNameTotalMap (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) := { tot_map_name : @name B0 P0 -> @name B1 P1 ; tot_map_name_inv : @name B1 P1 -> @name B0 P0 }.
Class MultiParamsNameTotalMapBijective `(M : MultiParamsNameTotalMap) : Prop := { tot_map_name_inv_inverse : forall n, tot_map_name_inv (tot_map_name n) = n ; tot_map_name_inverse_inv : forall n, tot_map_name (tot_map_name_inv n) = n ; }.
Class MultiParamsMsgTotalMap (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) := { tot_map_msg : @msg B0 P0 -> @msg B1 P1 }.
Section TotalMapDefs.
Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsTotalMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgTotalMap multi_fst multi_snd}.
Definition tot_map_name_msgs := map (fun nm => (tot_map_name (fst nm), tot_map_msg (snd nm))).
Definition tot_mapped_net_handlers me src m st := let '(out, st', ps) := net_handlers me src m st in (map tot_map_output out, tot_map_data st', tot_map_name_msgs ps).
Definition tot_mapped_input_handlers me inp st := let '(out, st', ps) := input_handlers me inp st in (map tot_map_output out, tot_map_data st', tot_map_name_msgs ps).
End TotalMapDefs.
Class MultiParamsTotalMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (B : BaseParamsTotalMap B0 B1) (N : MultiParamsNameTotalMap P0 P1) (P : MultiParamsMsgTotalMap P0 P1) : Prop := { tot_init_handlers_eq : forall n, tot_map_data (init_handlers n) = init_handlers (tot_map_name n) ; tot_net_handlers_eq : forall me src m st, tot_mapped_net_handlers me src m st = net_handlers (tot_map_name me) (tot_map_name src) (tot_map_msg m) (tot_map_data st) ; tot_input_handlers_eq : forall me inp st, tot_mapped_input_handlers me inp st = input_handlers (tot_map_name me) (tot_map_input inp) (tot_map_data st) }.
Class FailureParamsTotalMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (F0 : FailureParams P0) (F1 : FailureParams P1) (B : BaseParamsTotalMap B0 B1) : Prop := { tot_reboot_eq : forall d, tot_map_data (reboot d) = reboot (tot_map_data d) }.
Class NameOverlayParamsTotalMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (O0 : NameOverlayParams P0) (O1 : NameOverlayParams P1) (N : MultiParamsNameTotalMap P0 P1) : Prop := { tot_adjacent_to_fst_snd : forall n n', adjacent_to n n' <-> adjacent_to (tot_map_name n) (tot_map_name n') }.
Class FailMsgParamsTotalMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (F0 : FailMsgParams P0) (F1 : FailMsgParams P1) (P : MultiParamsMsgTotalMap P0 P1) : Prop := { tot_fail_msg_fst_snd : msg_fail = tot_map_msg msg_fail }.
Class NewMsgParamsTotalMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (N0 : NewMsgParams P0) (N1 : NewMsgParams P1) (P : MultiParamsMsgTotalMap P0 P1) : Prop := { tot_new_msg_fst_snd : msg_new = tot_map_msg msg_new }.
Section TotalMapBijective.
Context `{MB : MultiParamsNameTotalMapBijective}.
End TotalMapBijective.
Section TotalMapSimulations.
Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsTotalMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgTotalMap multi_fst multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsTotalMapCongruency base_map name_map msg_map}.
Definition tot_map_trace_occ (e : @name _ multi_fst * (@input base_fst + list (@output base_fst))) := match e with | (n, inl io) => (tot_map_name n, inl (tot_map_input io)) | (n, inr lo) => (tot_map_name n, inr (map tot_map_output lo)) end.
Definition tot_map_packet (p : @packet base_fst multi_fst) := match p with | mkPacket src dst m => mkPacket (tot_map_name src) (tot_map_name dst) (tot_map_msg m) end.
Definition tot_map_net (net : @network _ multi_fst) : @network _ multi_snd := {| nwPackets := map tot_map_packet net.(nwPackets) ; nwState := fun n => tot_map_data (net.(nwState) (tot_map_name_inv n)) |}.
Hypothesis tot_map_output_injective : forall o o', tot_map_output o = tot_map_output o' -> o = o'.
Context {fail_fst : FailureParams multi_fst}.
Context {fail_snd : FailureParams multi_snd}.
Context {fail_map_congr : FailureParamsTotalMapCongruency fail_fst fail_snd base_map}.
Context {overlay_fst : NameOverlayParams multi_fst}.
Context {overlay_snd : NameOverlayParams multi_snd}.
Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.
Context {fail_msg_fst : FailMsgParams multi_fst}.
Context {fail_msg_snd : FailMsgParams multi_snd}.
Context {fail_msg_map_congr : FailMsgParamsTotalMapCongruency fail_msg_fst fail_msg_snd msg_map}.
Definition tot_map_onet (onet : @ordered_network _ multi_fst) : @ordered_network _ multi_snd := {| onwPackets := fun src dst => map tot_map_msg (onet.(onwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ; onwState := fun n => tot_map_data (onet.(onwState) (tot_map_name_inv n)) |}.
Definition tot_map_trace (e : @name _ multi_fst * (@input base_fst + (@output base_fst))) := match e with | (n, inl i) => (tot_map_name n, inl (tot_map_input i)) | (n, inr o) => (tot_map_name n, inr (tot_map_output o)) end.
Context {new_msg_fst : NewMsgParams multi_fst}.
Context {new_msg_snd : NewMsgParams multi_snd}.
Context {new_msg_map_congr : NewMsgParamsTotalMapCongruency new_msg_fst new_msg_snd msg_map}.
Definition tot_map_odnet (net : @ordered_dynamic_network _ multi_fst) : @ordered_dynamic_network _ multi_snd := {| odnwNodes := map tot_map_name net.(odnwNodes) ; odnwPackets := fun src dst => map tot_map_msg (net.(odnwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ; odnwState := fun n => match net.(odnwState) (tot_map_name_inv n) with | None => None | Some d => Some (tot_map_data d) end |}.
End TotalMapSimulations.

Lemma tot_map_in_in : forall n m l, (forall nm, In nm l -> snd nm = m) -> ~ In (n, m) l -> ~ In (tot_map_name n, tot_map_msg m) (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l).
Proof using name_map_bijective.
move => n m.
elim => //=.
case => /= n' m' l IH H_eq H_in.
move => H_in'.
case: H_in' => H_in'.
inversion H_in'.
have H_nm := H_eq (n', m').
rewrite /= in H_nm.
case: H_in.
left.
apply tot_map_name_injective in H0.
rewrite H0.
rewrite H_nm //.
by left.
contradict H_in'.
apply: IH.
move => nm H_in_nm.
apply: H_eq.
by right.
move => H_in_nm.
case: H_in.
Admitted.

Lemma msg_in_map : forall m l n m', (forall nm, In nm l -> snd nm = m) -> In (tot_map_name n, tot_map_msg m') (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l) -> tot_map_msg m' = tot_map_msg m.
Proof using.
move => m.
elim => //=.
case => /= n m' l IH n' m0 H_in H_in_map.
have H_in_f := H_in (n, m').
rewrite /= in H_in_f.
case: H_in_map => H_in_map.
inversion H_in_map.
rewrite H_in_f //.
by left.
move: H_in_map.
apply: IH.
move => nm H_in'.
apply: H_in.
Admitted.

Lemma nodup_tot_map : forall m nms, (forall nm, In nm nms -> snd nm = m) -> NoDup nms -> NoDup (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) nms).
Proof using name_map_bijective.
move => m'.
elim => /=.
move => H_fail H_nd.
exact: NoDup_nil.
case => n m l IH H_fail H_nd.
inversion H_nd.
rewrite /=.
apply NoDup_cons.
have H_f := H_fail (n, m).
rewrite /= in H_f.
move => H_in.
have H_inf := @msg_in_map m' _ _ _ _ H_in.
rewrite H_inf in H_in.
contradict H_in.
apply tot_map_in_in.
move => nm H_in_nm.
apply: H_fail.
by right.
rewrite H_f // in H1.
by left.
move => nm H_in_f.
apply: H_fail.
by right.
apply: IH => //.
move => nm H_in_nm.
apply: H_fail.
Admitted.

Lemma in_tot_map_name : forall m l n, (forall nm, In nm l -> snd nm = m) -> In (n, tot_map_msg m) (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l) -> In (tot_map_name_inv n, m) l.
Proof using name_map_bijective.
move => m.
elim => //=.
case => /= n m' l IH n' H_in H_in'.
case: H_in' => H_in'.
inversion H_in'.
rewrite tot_map_name_inv_inverse.
have H_nm := H_in (n, m').
rewrite -H_nm /=; first by left.
by left.
right.
apply: IH => //.
move => nm H_inn.
apply: H_in.
Admitted.

Lemma in_map_pair_adjacent_to : forall (m : @msg _ multi_fst) ns failed h n, In (tot_map_name_inv n, m) (map2snd m (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns))) -> In (tot_map_name_inv n) (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns)).
Proof using.
move => m.
elim => //= [|n l IH] failed h n'; first by rewrite remove_all_nil.
have H_cn := remove_all_cons name_eq_dec failed n l.
break_or_hyp; break_and; find_rewrite; first exact: IH.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec' /=.
move => H_in.
case: H_in => H_in.
inversion H_in.
by left.
right.
exact: IH.
Admitted.

Lemma in_adjacent_exclude_in_exlude : forall ns failed n h, In (tot_map_name_inv n) (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns)) -> In (tot_map_name_inv n) (remove_all name_eq_dec failed ns) /\ adjacent_to h (tot_map_name_inv n).
Proof using.
elim => [|n l IH] failed n' h; first by rewrite remove_all_nil.
have H_cn := remove_all_cons name_eq_dec failed n l.
break_or_hyp; break_and; find_rewrite; first exact: IH.
rewrite /=.
case (adjacent_to_dec _ _) => /= H_dec'.
move => H_in.
case: H_in => H_in.
rewrite {1}H_in -{4}H_in.
split => //.
by left.
apply IH in H_in.
move: H_in => [H_eq H_in].
split => //.
by right.
move => H_in.
apply IH in H_in.
move: H_in => [H_eq H_in].
split => //.
Admitted.

Lemma in_failed_exclude : forall ns failed n, In (tot_map_name_inv n) (remove_all name_eq_dec failed ns) -> ~ In (tot_map_name_inv n) failed /\ In (tot_map_name_inv n) ns.
Proof using.
elim => [|n ns IH] failed n'; first by rewrite remove_all_nil.
have H_cn := remove_all_cons name_eq_dec failed n ns.
break_or_hyp; break_and; find_rewrite.
move => H_in.
apply IH in H_in.
move: H_in => [H_in H_in'].
split => //.
by right.
move => H_in.
case: H_in => H_in.
rewrite -{1}H_in {2}H_in.
split => //.
by left.
apply IH in H_in.
move: H_in => [H_in H_in'].
split => //.
Admitted.

Lemma in_in_adj_map_pair : forall (m : msg) ns failed n h, In n ns -> ~ In n (map tot_map_name failed) -> adjacent_to h n -> In (n, m) (map2snd m (filter_rel adjacent_to_dec h (remove_all name_eq_dec (map tot_map_name failed) ns))).
Proof using.
move => m.
elim => //=.
move => n ns IH failed n' h.
set mfailed := map _ failed.
move => H_in H_in' H_adj.
have H_cn := remove_all_cons name_eq_dec mfailed n ns.
break_or_hyp; break_and; find_rewrite.
break_or_hyp => //.
exact: IH.
case: H_in => H_in.
rewrite H_in.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec' //.
rewrite /=.
by left.
rewrite /=.
case (adjacent_to_dec _ _) => H_dec'.
rewrite /=.
right.
exact: IH.
Admitted.

Lemma in_exclude_not_in_failed_map : forall ns n failed, In n (remove_all name_eq_dec (map tot_map_name failed) ns) -> ~ In n (map tot_map_name failed) /\ In n ns.
Proof using.
elim => [|n ns IH] n' failed; first by rewrite remove_all_nil.
set mfailed := map _ failed.
have H_cn := remove_all_cons name_eq_dec mfailed n ns.
break_or_hyp; break_and; find_rewrite.
move => H_in.
apply IH in H_in.
move: H_in => [H_nin H_in].
split => //.
by right.
rewrite /=.
move => H_in.
case: H_in => H_in.
rewrite H_in.
subst.
split => //.
by left.
apply IH in H_in.
move: H_in => [H_nin H_in].
split => //.
Admitted.

Lemma not_in_map_not_in_failed : forall failed n, ~ In n (map tot_map_name failed) -> ~ In (tot_map_name_inv n) failed.
Proof using name_map_bijective.
elim => //=.
move => n ns IH n' H_in H_in'.
case: H_in' => H_in'.
case: H_in.
left.
by rewrite H_in' tot_map_name_inverse_inv.
contradict H_in'.
apply: IH.
move => H_in'.
case: H_in.
Admitted.

Lemma adjacent_in_in_msg : forall (m : @msg base_fst multi_fst) ns n h, adjacent_to h (tot_map_name_inv n) -> In (tot_map_name_inv n) ns -> In (tot_map_name_inv n, m) (map2snd m (filter_rel adjacent_to_dec h ns)).
Proof using.
move => m.
elim => //=.
move => n ns IH n' h H_adj H_in.
case (adjacent_to_dec _ _) => H_dec; case: H_in => H_in.
-
rewrite /=.
left.
by rewrite H_in.
-
rewrite /=.
right.
exact: IH.
-
by rewrite H_in in H_dec.
-
Admitted.

Lemma not_in_failed_in_exclude : forall ns n failed, ~ In (tot_map_name_inv n) failed -> In (tot_map_name_inv n) ns -> In (tot_map_name_inv n) (remove_all name_eq_dec failed ns).
Proof using.
elim => //=.
move => n ns IH n' failed H_in H_in'.
have H_cn := remove_all_cons name_eq_dec failed n ns.
break_or_hyp; break_and; find_rewrite; break_or_hyp => //=.
-
exact: IH.
-
by left.
-
Admitted.

Lemma tot_map_name_in : forall ns n, In (tot_map_name n) (map tot_map_name ns) -> In n ns.
Proof using name_map_bijective.
elim => //=.
move => n' ns IH n H_in.
case: H_in => H_in.
left.
exact: tot_map_name_injective.
right.
Admitted.

Lemma nodup_perm_map_map_pair_perm : forall h m failed ns ns', NoDup ns -> Permutation (map tot_map_name ns) ns' -> Permutation (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) (map2snd m (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns)))) (map2snd (tot_map_msg m) (filter_rel adjacent_to_dec (tot_map_name h) (remove_all name_eq_dec (map tot_map_name failed) ns'))).
Proof using overlay_map_congr name_map_bijective.
move => h m failed ns ns' H_nd H_pm.
apply NoDup_Permutation; last split.
-
apply (@nodup_tot_map m); first exact: in_map2snd_snd.
apply NoDup_map2snd.
by apply NoDup_remove_all.
-
apply NoDup_map2snd.
apply NoDup_remove_all.
move: H_pm.
apply: NoDup_Permutation_NoDup.
exact: nodup_to_map_name.
-
case: x => n m' H_in.
have H_eq := tot_map_in_snd _ _ _ _ H_in.
rewrite /= in H_eq.
rewrite H_eq in H_in.
rewrite H_eq {H_eq}.
apply in_tot_map_name in H_in.
apply in_map2snd_related_in in H_in.
move: H_in => [H_adj H_in].
apply in_failed_exclude in H_in.
move: H_in => [H_in H_in'].
have H_nin: ~ In n (map tot_map_name failed).
rewrite -(tot_map_name_inverse_inv n).
exact: not_in_failed_not_in.
apply tot_adjacent_to_fst_snd in H_adj.
rewrite tot_map_name_inverse_inv in H_adj.
have H_inn: In n ns'.
apply (Permutation_in n) in H_pm => //.
rewrite -(tot_map_name_inverse_inv n).
exact: in_failed_in.
exact: in_in_adj_map_pair.
exact: in_map2snd_snd.
-
case: x => n m' H_in.
have H_eq := in_map2snd_snd _ _ adjacent_to adjacent_to_dec _ _ _ _ H_in.
rewrite /= in H_eq.
rewrite H_eq.
rewrite H_eq in H_in.
apply in_map2snd_related_in in H_in.
move: H_in => [H_adj H_in].
rewrite -(tot_map_name_inverse_inv n) in H_adj.
apply tot_adjacent_to_fst_snd in H_adj.
apply in_exclude_not_in_failed_map in H_in.
move: H_in => [H_in_f H_in].
apply not_in_map_not_in_failed in H_in_f.
have H_in_n: In (tot_map_name_inv n) ns.
apply Permutation_sym in H_pm.
apply (Permutation_in n) in H_pm => //.
apply: tot_map_name_in.
by rewrite tot_map_name_inverse_inv.
apply in_tot_map_msg; first by move => nm; apply in_map2snd_snd.
apply: adjacent_in_in_msg => //.
Admitted.

Lemma map_map_pair_eq : forall h m failed, Permutation (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) (map2snd m (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed nodes)))) (map2snd (tot_map_msg m) (filter_rel adjacent_to_dec (tot_map_name h) (remove_all name_eq_dec (map tot_map_name failed) nodes))).
Proof using overlay_map_congr name_map_bijective.
move => h m failed.
apply nodup_perm_map_map_pair_perm; first exact: no_dup_nodes.
apply Permutation_sym.
Admitted.

Lemma map_msg_fail_eq_nodup : forall h failed ns ns', NoDup ns -> Permutation (map tot_map_name ns) ns' -> Permutation (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) (map2snd msg_fail (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed ns)))) (map2snd msg_fail (filter_rel adjacent_to_dec (tot_map_name h) (remove_all name_eq_dec (map tot_map_name failed) ns'))).
Proof using overlay_map_congr name_map_bijective fail_msg_map_congr.
move => h failed.
rewrite tot_fail_msg_fst_snd.
Admitted.

Lemma map_msg_fail_eq : forall h failed, Permutation (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) (map2snd msg_fail (filter_rel adjacent_to_dec h (remove_all name_eq_dec failed nodes)))) (map2snd msg_fail (filter_rel adjacent_to_dec (tot_map_name h) (remove_all name_eq_dec (map tot_map_name failed) nodes))).
Proof using overlay_map_congr name_map_bijective fail_msg_map_congr.
move => h failed.
rewrite tot_fail_msg_fst_snd.
Admitted.

Lemma map_msg_update2 : forall f ms to from, (fun src dst => map tot_map_msg (update2 name_eq_dec f from to ms (tot_map_name_inv src) (tot_map_name_inv dst))) = update2 name_eq_dec (fun src0 dst0 : name => map tot_map_msg (f (tot_map_name_inv src0) (tot_map_name_inv dst0))) (tot_map_name from) (tot_map_name to) (map tot_map_msg ms).
Proof using name_map_bijective.
move => f ms to from.
apply functional_extensionality => src.
apply functional_extensionality => dst.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec; case (sumbool_and _ _ _ _) => H_dec' //.
move: H_dec => [H_eq H_eq'].
case: H_dec' => H_dec'.
rewrite H_eq in H_dec'.
by rewrite tot_map_name_inverse_inv in H_dec'.
rewrite H_eq' in H_dec'.
by rewrite tot_map_name_inverse_inv in H_dec'.
move: H_dec' => [H_eq H_eq'].
case: H_dec => H_dec.
rewrite -H_eq in H_dec.
by rewrite tot_map_name_inv_inverse in H_dec.
rewrite -H_eq' in H_dec.
Admitted.

Lemma collate_tot_map_eq : forall f h l, (fun src dst => map tot_map_msg (collate name_eq_dec h f l (tot_map_name_inv src) (tot_map_name_inv dst))) = collate name_eq_dec (tot_map_name h) (fun src dst => map tot_map_msg (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name_msgs l).
Proof using name_map_bijective.
move => f h l.
elim: l h f => //.
case => n m l IH h f.
rewrite /= IH /=.
rewrite 2!tot_map_name_inv_inverse /=.
set f1 := fun _ _ => _.
set f2 := update2 _ _ _ _ _.
have H_eq_f: f1 = f2.
rewrite /f1 /f2 {f1 f2}.
have H_eq := map_msg_update2 f (f h n ++ [m]) n h.
rewrite map_app in H_eq.
by rewrite H_eq.
Admitted.

Lemma collate_tot_map_update2_eq : forall f from to ms l, (fun src dst => map tot_map_msg (collate name_eq_dec to (update2 name_eq_dec f from to ms) l (tot_map_name_inv src) (tot_map_name_inv dst))) = collate name_eq_dec (tot_map_name to) (update2 name_eq_dec (fun src dst : name => map tot_map_msg (f (tot_map_name_inv src) (tot_map_name_inv dst))) (tot_map_name from) (tot_map_name to) (map tot_map_msg ms)) (tot_map_name_msgs l).
Proof using name_map_bijective.
move => f from to ms l.
rewrite -map_msg_update2.
Admitted.

Lemma in_tot_map_msg : forall m l n, (forall nm, In nm l -> snd nm = m) -> In (tot_map_name_inv n, m) l -> In (n, tot_map_msg m) (map (fun nm : name * msg => (tot_map_name (fst nm), tot_map_msg (snd nm))) l).
Proof using name_map_bijective.
move => m.
elim => //=.
case => n m' /= l IH n' H_in H_in'.
case: H_in' => H_in'.
inversion H_in'.
left.
by rewrite tot_map_name_inverse_inv.
right.
apply: IH => //.
move => nm H_inn.
apply: H_in.
by right.

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

Theorem step_ordered_dynamic_failure_tot_mapped_simulation_1 : forall net net' failed failed' tr, NoDup (odnwNodes net) -> @step_ordered_dynamic_failure _ _ overlay_fst new_msg_fst fail_msg_fst (failed, net) (failed', net') tr -> @step_ordered_dynamic_failure _ _ overlay_snd new_msg_snd fail_msg_snd (map tot_map_name failed, tot_map_odnet net) (map tot_map_name failed', tot_map_odnet net') (map tot_map_trace tr).
Proof using overlay_map_congr new_msg_map_congr name_map_bijective multi_map_congr fail_msg_map_congr.
move => net net' failed failed' tr H_nd H_step.
invcs H_step.
-
rewrite /tot_map_odnet /=.
apply (@StepOrderedDynamicFailure_start _ _ _ _ _ _ _ _ (tot_map_name h)) => /=; first exact: not_in_failed_not_in.
set p1 := fun _ _ => _.
set p2 := collate_ls _ _ _ _ _.
set s1 := fun _ => _.
set s2 := update _ _ _ _.
have H_eq_s: s1 = s2.
rewrite /s1 /s2 /update {s1 s2}.
apply functional_extensionality => n.
rewrite -tot_init_handlers_eq.
break_match_goal.
break_if; break_if; try by congruence.
-
by repeat find_rewrite; repeat find_rewrite_lem tot_map_name_inv_inverse.
-
by find_reverse_rewrite; find_rewrite_lem tot_map_name_inverse_inv.
-
by find_rewrite.
break_if; break_if; (try by congruence); last by find_rewrite.
by repeat find_rewrite; repeat find_rewrite_lem tot_map_name_inv_inverse.
rewrite H_eq_s /s2 {s1 s2 H_eq_s}.
have H_eq_p: p1 = p2.
rewrite /p1 /p2 {p1 p2}.
rewrite collate_ls_tot_map_eq /=.
rewrite collate_tot_map_eq.
rewrite tot_new_msg_fst_snd.
set f1 := fun _ _ => _.
set c1 := collate _ _ _ _.
set c2 := collate _ _ _ _.
set f'1 := map tot_map_name _.
set f'2 := filter_rel _ (tot_map_name h) _.
have H_c: c1 = c2.
rewrite /c1 /c2 {c1 c2}.
apply: NoDup_Permutation_collate_eq; last first.
rewrite /tot_map_name_msgs.
by apply: nodup_perm_map_map_pair_perm; last exact: Permutation_refl.
rewrite /tot_map_name_msgs /=.
apply: NoDup_map_snd_fst => //.
apply (@nodup_tot_map msg_new); first exact: in_map2snd_snd.
apply: NoDup_map2snd.
exact: NoDup_remove_all.
move => nm nm' H_in H_in'.
apply tot_map_in_snd in H_in.
apply tot_map_in_snd in H_in'.
by rewrite H_in H_in'.
rewrite H_c {H_c}.
suff H_suff: f'1 = f'2 by rewrite H_suff.
rewrite /f'1 /f'2.
elim (odnwNodes net) => /=; first by rewrite 2!remove_all_nil.
move => n ns.
set mn := tot_map_name n.
set mns := map _ ns.
set mfailed' := map _ failed'.
move => IH.
have H_cn := remove_all_cons name_eq_dec failed' n ns.
have H_cn' := remove_all_cons name_eq_dec mfailed' mn mns.
unfold mn, mns, mfailed' in *.
repeat break_or_hyp; repeat break_and; repeat find_rewrite => //=.
*
by find_apply_lem_hyp not_in_failed_not_in.
*
by find_apply_lem_hyp in_failed_in.
*
case adjacent_to_dec => H_dec; case adjacent_to_dec => H_dec' => //=.
+
by rewrite IH.
+
by find_apply_lem_hyp tot_adjacent_to_fst_snd.
+
by find_apply_lem_hyp tot_adjacent_to_fst_snd.
by rewrite H_eq_p.
-
rewrite /tot_map_odnet /=.
apply (@StepOrderedDynamicFailure_deliver _ _ _ _ _ _ _ _ _ (tot_map_msg m) (map tot_map_msg ms) (map tot_map_output out) (tot_map_data d) (tot_map_data d') (tot_map_name_msgs l) (tot_map_name from) (tot_map_name to)) => //=.
*
exact: not_in_failed_not_in.
*
exact: in_failed_in.
*
rewrite tot_map_name_inv_inverse.
by break_match; congruence.
*
rewrite 2!tot_map_name_inv_inverse.
by find_rewrite.
*
rewrite -tot_net_handlers_eq /tot_mapped_net_handlers.
repeat break_let.
by repeat tuple_inversion.
*
set u1 := fun _ => match _ with | _ => _ end.
set u2 := update _ _ _ _.
rewrite collate_tot_map_update2_eq.
suff H_suff: u1 = u2 by rewrite H_suff.
rewrite /u1 /u2 /update /=.
apply functional_extensionality => n.
repeat break_if; try by congruence.
rewrite -(tot_map_name_inverse_inv n) in n0.
by rewrite e in n0.
find_rewrite.
by find_rewrite_lem tot_map_name_inv_inverse.
*
by rewrite map_tot_map_trace_eq.
-
rewrite /tot_map_odnet /=.
apply (@StepOrderedDynamicFailure_input _ _ _ _ _ (tot_map_name h) _ _ _ _ (map tot_map_output out) (tot_map_input inp) (tot_map_data d) (tot_map_data d') (tot_map_name_msgs l)) => //=.
*
exact: not_in_failed_not_in.
*
exact: in_failed_in.
*
rewrite tot_map_name_inv_inverse.
by break_match; congruence.
*
rewrite /= -tot_input_handlers_eq /tot_mapped_input_handlers.
repeat break_let.
by repeat tuple_inversion.
*
rewrite collate_tot_map_eq.
set u1 := fun _ => match _ with | _ => _ end.
set u2 := update _ _ _ _.
suff H_suff: u1 = u2 by rewrite H_suff.
rewrite /u1 /u2 /update /=.
apply functional_extensionality => n.
repeat break_if; try by congruence.
rewrite -(tot_map_name_inverse_inv n) in n0.
by rewrite e in n0.
find_rewrite.
by find_rewrite_lem tot_map_name_inv_inverse.
*
by rewrite map_tot_map_trace_eq.
-
rewrite /tot_map_odnet /=.
set l := map2snd _ _.
have H_nd': NoDup (map (fun nm => fst nm) (tot_map_name_msgs l)).
rewrite /tot_map_name_msgs /=.
rewrite /l {l}.
apply NoDup_map_snd_fst.
apply (@nodup_tot_map msg_fail); first exact: in_map2snd_snd.
apply NoDup_map2snd.
exact: NoDup_remove_all.
move => nm nm' H_in H_in'.
have H_fail := tot_map_in_snd _ _ _ _ H_in.
have H_fail' := tot_map_in_snd _ _ _ _ H_in'.
by rewrite H_fail H_fail'.
have H_pm := map_msg_fail_eq_nodup h failed H_nd (Permutation_refl (map tot_map_name (odnwNodes net))).
have H_eq := NoDup_Permutation_collate_eq _ _ name_eq_dec _ _ _ _ H_nd' H_pm.
rewrite /l /tot_map_name_msgs in H_eq.
apply: StepOrderedDynamicFailure_fail.
*
exact: not_in_failed_not_in.
*
exact: in_failed_in.
*
rewrite /=.
rewrite /l collate_tot_map_eq /tot_map_name_msgs.
by rewrite H_eq.

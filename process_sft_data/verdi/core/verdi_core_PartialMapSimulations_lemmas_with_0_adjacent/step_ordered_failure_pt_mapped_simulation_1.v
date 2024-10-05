Require Import Verdi.Verdi.
Require Import Verdi.DynamicNetLemmas.
Require Import Verdi.TotalMapSimulations.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import FunctionalExtensionality.
Require Import Sumbool.
Require Import Sorting.Permutation.
Require Import Verdi.DynamicNetLemmas.
Require Import Verdi.Ssrexport.
Set Implicit Arguments.
Class BaseParamsPartialMap (P0 : BaseParams) (P1 : BaseParams) := { pt_map_data : @data P0 -> @data P1 ; pt_map_input : @input P0 -> option (@input P1) ; pt_map_output : @output P0 -> option (@output P1) }.
Class MultiParamsMsgPartialMap (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) := { pt_map_msg : @msg B0 P0 -> option (@msg B1 P1) }.
Section PartialMapDefs.
Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsPartialMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgPartialMap multi_fst multi_snd}.
Definition pt_map_name_msg nm := match pt_map_msg (snd nm) with | Some m => Some (tot_map_name (fst nm), m) | None => None end.
Definition pt_mapped_net_handlers me src m st := let '(out, st', ps) := net_handlers me src m st in (filterMap pt_map_output out, pt_map_data st', filterMap pt_map_name_msg ps).
Definition pt_mapped_input_handlers me inp st := let '(out, st', ps) := input_handlers me inp st in (filterMap pt_map_output out, pt_map_data st', filterMap pt_map_name_msg ps).
End PartialMapDefs.
Class MultiParamsPartialMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (B : BaseParamsPartialMap B0 B1) (N : MultiParamsNameTotalMap P0 P1) (P : MultiParamsMsgPartialMap P0 P1) : Prop := { pt_init_handlers_eq : forall n, pt_map_data (init_handlers n) = init_handlers (tot_map_name n) ; pt_net_handlers_some : forall me src m st m', pt_map_msg m = Some m' -> pt_mapped_net_handlers me src m st = net_handlers (tot_map_name me) (tot_map_name src) m' (pt_map_data st) ; pt_net_handlers_none : forall me src m st out st' ps, pt_map_msg m = None -> net_handlers me src m st = (out, st', ps) -> pt_map_data st' = pt_map_data st /\ filterMap pt_map_name_msg ps = [] /\ filterMap pt_map_output out = [] ; pt_input_handlers_some : forall me inp st inp', pt_map_input inp = Some inp' -> pt_mapped_input_handlers me inp st = input_handlers (tot_map_name me) inp' (pt_map_data st) ; pt_input_handlers_none : forall me inp st out st' ps, pt_map_input inp = None -> input_handlers me inp st = (out, st', ps) -> pt_map_data st' = pt_map_data st /\ filterMap pt_map_name_msg ps = [] /\ filterMap pt_map_output out = [] }.
Class FailureParamsPartialMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (F0 : FailureParams P0) (F1 : FailureParams P1) (B : BaseParamsPartialMap B0 B1) : Prop := { pt_reboot_eq : forall d, pt_map_data (reboot d) = reboot (pt_map_data d) }.
Class FailMsgParamsPartialMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (F0 : FailMsgParams P0) (F1 : FailMsgParams P1) (P : MultiParamsMsgPartialMap P0 P1) : Prop := { pt_fail_msg_fst_snd : pt_map_msg msg_fail = Some msg_fail }.
Class NewMsgParamsPartialMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (N0 : NewMsgParams P0) (N1 : NewMsgParams P1) (P : MultiParamsMsgPartialMap P0 P1) : Prop := { pt_new_msg_fst_snd : pt_map_msg msg_new = Some msg_new }.
Section PartialMapSimulations.
Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {base_map : BaseParamsPartialMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgPartialMap multi_fst multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsPartialMapCongruency base_map name_map msg_map}.
Definition pt_map_trace_occ (e : @name _ multi_fst * (@input base_fst + list (@output base_fst))) : option (@name _ multi_snd * (@input base_snd + list (@output base_snd))) := match e with | (n, inl io) => match pt_map_input io with | Some io' => Some (tot_map_name n, inl io') | None => None end | (n, inr out) => Some (tot_map_name n, inr (filterMap pt_map_output out)) end.
Definition pt_map_packet (p : @packet _ multi_fst) := match p with | mkPacket src dst m => match pt_map_msg m with | Some m' => Some (mkPacket (tot_map_name src) (tot_map_name dst) m') | None => None end end.
Definition pt_map_net (net : @network _ multi_fst) : @network _ multi_snd := {| nwPackets := filterMap pt_map_packet net.(nwPackets) ; nwState := fun n => pt_map_data (net.(nwState) (tot_map_name_inv n)) |}.
Context {fail_fst : FailureParams multi_fst}.
Context {fail_snd : FailureParams multi_snd}.
Context {fail_map_congr : FailureParamsPartialMapCongruency fail_fst fail_snd base_map}.
Definition pt_map_onet (onet : @ordered_network _ multi_fst) : @ordered_network _ multi_snd := {| onwPackets := fun src dst => filterMap pt_map_msg (onet.(onwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ; onwState := fun n => pt_map_data (onet.(onwState) (tot_map_name_inv n)) |}.
Definition pt_map_trace_ev (e : @name _ multi_fst * (@input base_fst + (@output base_fst))) : option (@name _ multi_snd * (@input base_snd + (@output base_snd))) := match e with | (n, inl i) => match pt_map_input i with | Some i' => Some (tot_map_name n, inl i') | None => None end | (n, inr o) => match pt_map_output o with | Some o' => Some (tot_map_name n, inr o') | None => None end end.
Context {overlay_fst : NameOverlayParams multi_fst}.
Context {overlay_snd : NameOverlayParams multi_snd}.
Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.
Context {fail_msg_fst : FailMsgParams multi_fst}.
Context {fail_msg_snd : FailMsgParams multi_snd}.
Context {fail_msg_map_congr : FailMsgParamsPartialMapCongruency fail_msg_fst fail_msg_snd msg_map}.
Context {new_msg_fst : NewMsgParams multi_fst}.
Context {new_msg_snd : NewMsgParams multi_snd}.
Context {new_msg_map_congr : NewMsgParamsPartialMapCongruency new_msg_fst new_msg_snd msg_map}.
Definition pt_map_odnet (net : @ordered_dynamic_network _ multi_fst) : @ordered_dynamic_network _ multi_snd := {| odnwNodes := map tot_map_name net.(odnwNodes) ; odnwPackets := fun src dst => filterMap pt_map_msg (net.(odnwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ; odnwState := fun n => match net.(odnwState) (tot_map_name_inv n) with | None => None | Some d => Some (pt_map_data d) end |}.
Hypothesis pt_map_msg_injective : forall m0 m1 m, pt_map_msg m0 = Some m -> pt_map_msg m1 = Some m -> m0 = m1.
End PartialMapSimulations.

Theorem step_ordered_failure_pt_mapped_simulation_1 : forall net net' failed failed' tr, @step_ordered_failure _ _ overlay_fst fail_msg_fst (failed, net) (failed', net') tr -> @step_ordered_failure _ _ overlay_snd fail_msg_snd (map tot_map_name failed, pt_map_onet net) (map tot_map_name failed', pt_map_onet net') (filterMap pt_map_trace_ev tr) \/ pt_map_onet net' = pt_map_onet net /\ failed = failed' /\ filterMap pt_map_trace_ev tr = [].
Proof using overlay_map_congr name_map_bijective multi_map_congr fail_msg_map_congr.
move => net net' failed failed' tr H_step.
invcs H_step.
-
destruct (pt_map_msg m) eqn:?.
left.
rewrite /pt_map_onet /=.
apply (@StepOrderedFailure_deliver _ _ _ _ _ _ _ _ m0 (filterMap pt_map_msg ms) (filterMap pt_map_output out) (pt_map_data d) (filterMap pt_map_name_msg l) (tot_map_name from) (tot_map_name to)).
*
rewrite /= 2!tot_map_name_inv_inverse /=.
find_rewrite.
rewrite /=.
destruct (pt_map_msg _) eqn:?; rewrite Heqo in Heqo0 => //.
by inversion Heqo.
*
exact: not_in_failed_not_in.
*
rewrite /= -(pt_net_handlers_some _ _ _ _ Heqo) /pt_mapped_net_handlers /= tot_map_name_inv_inverse.
repeat break_let.
by find_inversion.
*
by rewrite /= pt_map_update_eq collate_pt_map_update2_eq.
*
by rewrite filterMap_pt_map_trace_ev_outputs_eq.
right.
have [H_eq_d [H_ms H_out]] := pt_net_handlers_none _ _ _ _ Heqo H5.
rewrite filterMap_pt_map_trace_ev_outputs_eq /= H_out /=.
split => //.
rewrite /pt_map_onet /= pt_map_update_eq H_eq_d collate_pt_map_update2_eq H_ms /=.
set nwP1 := update2 _ _ _ _ _.
set nwS1 := update _ _ _ _.
set nwP2 := fun _ _ => _.
set nwS2 := fun _ => _.
have H_eq_s: nwS1 = nwS2.
rewrite /nwS1 /nwS2 {nwS1 nwS2}.
apply functional_extensionality => n.
rewrite /update /=.
case (name_eq_dec _ _) => H_dec //.
by rewrite H_dec tot_map_name_inv_inverse.
have H_eq_p: nwP1 = nwP2.
rewrite /nwP1 /nwP2 /=.
apply functional_extensionality => src.
apply functional_extensionality => dst.
rewrite /update2 /=.
case (sumbool_and _ _ _ _) => H_dec //.
move: H_dec => [H_eq_from H_eq_to].
rewrite -H_eq_from -H_eq_to /= 2!tot_map_name_inv_inverse H3 /=.
case H_m': (pt_map_msg _) => [m'|] //.
by rewrite H_m' in Heqo.
by rewrite H_eq_s H_eq_p.
-
case H_i: (pt_map_input _) => [inp'|].
left.
apply (@StepOrderedFailure_input _ _ _ _ (tot_map_name h) _ _ _ _ (filterMap pt_map_output out) inp' (pt_map_data d) (filterMap pt_map_name_msg l)).
*
exact: not_in_failed_not_in.
*
rewrite /=.
have H_q := pt_input_handlers_some h inp (onwState net h) H_i.
rewrite /pt_mapped_input_handlers /= in H_q.
find_rewrite.
rewrite H_q.
by rewrite tot_map_name_inv_inverse.
*
by rewrite /pt_map_onet /= pt_map_update_eq collate_pt_map_eq.
*
by rewrite filterMap_pt_map_trace_ev_outputs_eq.
right.
rewrite /= /pt_map_onet /=.
have [H_d [H_l H_o]] := pt_input_handlers_none h inp (onwState net h) H_i H4.
rewrite filterMap_pt_map_trace_ev_outputs_eq H_o /=.
split => //.
rewrite pt_map_update_eq /= H_d.
rewrite collate_pt_map_eq H_l /=.
set nwS1 := update _ _ _ _.
set nwS2 := fun n => pt_map_data _.
have H_eq_n: nwS1 = nwS2.
rewrite /nwS1 /nwS2 /=.
apply functional_extensionality => n.
rewrite /update /=.
case (name_eq_dec _ _) => H_dec //.
by rewrite H_dec tot_map_name_inv_inverse.
by rewrite H_eq_n.
-
left.
rewrite /pt_map_onet /=.
set l := map2snd _ _.
have H_nd: NoDup (map fst (filterMap pt_map_name_msg l)).
rewrite /pt_map_name_msg /=.
rewrite /l {l}.
apply NoDup_map_snd_fst.
apply (@nodup_pt_map msg_fail); first exact: in_map2snd_snd.
apply NoDup_map2snd.
apply NoDup_remove_all.
exact: no_dup_nodes.
move => nm nm' H_in H_in'.
by rewrite (pt_map_in_snd _ _ _ _ pt_fail_msg_fst_snd H_in) (pt_map_in_snd _ _ _ _ pt_fail_msg_fst_snd H_in').
apply: StepOrderedFailure_fail => //.
*
exact: not_in_failed_not_in.
*
rewrite /= /l collate_pt_map_eq /=.
by rewrite (NoDup_Permutation_collate_eq _ _ name_eq_dec _ _ _ _ H_nd (pt_map_map_pair_eq msg_fail h failed pt_fail_msg_fst_snd)).

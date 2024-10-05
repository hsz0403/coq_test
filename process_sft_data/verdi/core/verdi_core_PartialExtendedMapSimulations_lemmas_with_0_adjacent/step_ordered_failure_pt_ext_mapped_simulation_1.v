Require Import Verdi.Verdi.
Require Import Verdi.DynamicNetLemmas.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import FunctionalExtensionality.
Require Import Sumbool.
Require Import Sorting.Permutation.
Require Import Verdi.Ssrexport.
Set Implicit Arguments.
Class MultiParamsPartialExtendedMap (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) := { pt_ext_map_data : @data B0 -> @name B0 P0 -> @data B1 ; pt_ext_map_input : @input B0 -> @name B0 P0 -> @data B0 -> option (@input B1) }.
Section PartialExtendedMapDefs.
Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgPartialMap multi_fst multi_snd}.
Context {multi_map : MultiParamsPartialExtendedMap multi_fst multi_snd}.
Definition pt_ext_mapped_net_handlers me src m st := let '(_, st', ps) := net_handlers me src m st in (pt_ext_map_data st' me, filterMap (pt_map_name_msg (name_map := name_map) (msg_map := msg_map)) ps).
Definition pt_ext_mapped_input_handlers me inp st := let '(_, st', ps) := input_handlers me inp st in (pt_ext_map_data st' me, filterMap (pt_map_name_msg (name_map := name_map) (msg_map := msg_map)) ps).
End PartialExtendedMapDefs.
Class MultiParamsPartialExtendedMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (N : MultiParamsNameTotalMap P0 P1) (P : MultiParamsMsgPartialMap P0 P1) (P : MultiParamsPartialExtendedMap P0 P1) : Prop := { pt_ext_init_handlers_eq : forall n, pt_ext_map_data (init_handlers n) n = init_handlers (tot_map_name n) ; pt_ext_net_handlers_some : forall me src m st m' out st' ps, pt_map_msg m = Some m' -> net_handlers (tot_map_name me) (tot_map_name src) m' (pt_ext_map_data st me) = (out, st', ps) -> pt_ext_mapped_net_handlers me src m st = (st', ps) ; pt_ext_net_handlers_none : forall me src m st out st' ps, pt_map_msg m = None -> net_handlers me src m st = (out, st', ps) -> pt_ext_map_data st' me = pt_ext_map_data st me /\ filterMap pt_map_name_msg ps = [] ; pt_ext_input_handlers_some : forall me inp st inp' out st' ps, pt_ext_map_input inp me st = Some inp' -> input_handlers (tot_map_name me) inp' (pt_ext_map_data st me) = (out, st', ps) -> pt_ext_mapped_input_handlers me inp st = (st', ps) ; pt_ext_input_handlers_none : forall me inp st out st' ps, pt_ext_map_input inp me st = None -> input_handlers me inp st = (out, st', ps) -> pt_ext_map_data st' me = pt_ext_map_data st me /\ filterMap pt_map_name_msg ps = [] }.
Class FailureParamsPartialExtendedMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : MultiParams B1) (F0 : FailureParams P0) (F1 : FailureParams P1) (P : MultiParamsPartialExtendedMap P0 P1) : Prop := { pt_ext_reboot_eq : forall d me, pt_ext_map_data (reboot d) me = reboot (pt_ext_map_data d me) }.
Section PartialExtendedMapSimulations.
Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi_fst : MultiParams base_fst}.
Context {multi_snd : MultiParams base_snd}.
Context {name_map : MultiParamsNameTotalMap multi_fst multi_snd}.
Context {msg_map : MultiParamsMsgPartialMap multi_fst multi_snd}.
Context {multi_map : MultiParamsPartialExtendedMap multi_fst multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsPartialExtendedMapCongruency name_map msg_map multi_map}.
Definition pt_ext_map_net (net : @network _ multi_fst) : @network _ multi_snd := {| nwPackets := filterMap pt_map_packet net.(nwPackets) ; nwState := fun n => pt_ext_map_data (net.(nwState) (tot_map_name_inv n)) (tot_map_name_inv n) |}.
Definition pt_ext_map_onet (onet : @ordered_network _ multi_fst) : @ordered_network _ multi_snd := mkONetwork (fun src dst => filterMap pt_map_msg (onet.(onwPackets) (tot_map_name_inv src) (tot_map_name_inv dst))) (fun n => pt_ext_map_data (onet.(onwState) (tot_map_name_inv n)) (tot_map_name_inv n)).
Context {overlay_fst : NameOverlayParams multi_fst}.
Context {overlay_snd : NameOverlayParams multi_snd}.
Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.
Context {fail_msg_fst : FailMsgParams multi_fst}.
Context {fail_msg_snd : FailMsgParams multi_snd}.
Context {fail_msg_map_congr : FailMsgParamsPartialMapCongruency fail_msg_fst fail_msg_snd msg_map}.
Context {new_msg_fst : NewMsgParams multi_fst}.
Context {new_msg_snd : NewMsgParams multi_snd}.
Context {new_msg_map_congr : NewMsgParamsPartialMapCongruency new_msg_fst new_msg_snd msg_map}.
Definition pt_ext_map_odnet (net : @ordered_dynamic_network _ multi_fst) : @ordered_dynamic_network _ multi_snd := {| odnwNodes := map tot_map_name net.(odnwNodes) ; odnwPackets := fun src dst => filterMap pt_map_msg (net.(odnwPackets) (tot_map_name_inv src) (tot_map_name_inv dst)) ; odnwState := fun n => match net.(odnwState) (tot_map_name_inv n) with | None => None | Some d => Some (pt_ext_map_data d (tot_map_name_inv n)) end |}.
End PartialExtendedMapSimulations.

Theorem step_ordered_failure_pt_ext_mapped_simulation_1 : forall net net' failed failed' tr, @step_ordered_failure _ _ overlay_fst fail_msg_fst (failed, net) (failed', net') tr -> (exists tr', @step_ordered_failure _ _ overlay_snd fail_msg_snd (map tot_map_name failed, pt_ext_map_onet net) (map tot_map_name failed', pt_ext_map_onet net') tr') \/ pt_ext_map_onet net' = pt_ext_map_onet net /\ failed = failed'.
Proof using overlay_map_congr name_map_bijective multi_map_congr fail_msg_map_congr.
move => net net' failed failed' tr H_step.
invcs H_step.
-
destruct (pt_map_msg m) eqn:?.
left.
destruct (net_handlers (tot_map_name to) (tot_map_name from) m0 (pt_ext_map_data (onwState net to) to)) eqn:?.
destruct p as [out' d'].
exists (map2fst (tot_map_name to) (map inr out')).
rewrite /pt_ext_map_onet /=.
apply (@StepOrderedFailure_deliver _ _ _ _ _ _ _ _ m0 (filterMap pt_map_msg ms) out' (pt_ext_map_data d to) (filterMap pt_map_name_msg l) (tot_map_name from) (tot_map_name to)) => //=.
*
rewrite 2!tot_map_name_inv_inverse /= H3 /=.
case H_m1: (pt_map_msg _) => [m1|]; last by rewrite Heqo in H_m1.
rewrite Heqo in H_m1.
by inversion H_m1.
*
exact: not_in_failed_not_in.
*
rewrite /= tot_map_name_inv_inverse.
have H_q := @pt_ext_net_handlers_some _ _ _ _ _ _ _ multi_map_congr _ _ _ _ _ _ _ _ Heqo Heqp.
rewrite /pt_ext_mapped_net_handlers /= in H_q.
by repeat break_let; repeat tuple_inversion.
*
by rewrite /= pt_ext_map_update_eq collate_pt_map_update2_eq.
right.
split => //.
have [H_eq_d H_ms] := pt_ext_net_handlers_none _ _ _ _ Heqo H5.
rewrite /pt_ext_map_onet /= pt_ext_map_update_eq H_eq_d collate_pt_map_update2_eq H_ms /=.
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
destruct (pt_ext_map_input inp h (onwState net h)) eqn:?.
left.
destruct (input_handlers (tot_map_name h) i (pt_ext_map_data (onwState net h) h)) eqn:?.
destruct p as [out' d'].
exists ((tot_map_name h, inl i) :: map2fst (tot_map_name h) (map inr out')).
apply (@StepOrderedFailure_input _ _ _ _ (tot_map_name h) _ _ _ _ out' i (pt_ext_map_data d h) (filterMap pt_map_name_msg l)) => //=.
*
exact: not_in_failed_not_in.
*
rewrite /= tot_map_name_inv_inverse.
have H_q := @pt_ext_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h inp (onwState net h) _ _ _ _ Heqo Heqp.
rewrite /pt_ext_mapped_input_handlers /= in H_q.
by repeat break_let; repeat tuple_inversion.
*
by rewrite /pt_ext_map_onet /= pt_ext_map_update_eq collate_pt_map_eq.
right.
rewrite /= /pt_ext_map_onet /=.
have [H_d H_l] := pt_ext_input_handlers_none h inp (onwState net h) Heqo H4.
split => //.
rewrite pt_ext_map_update_eq /= H_d.
rewrite collate_pt_map_eq H_l /=.
set nwS1 := update _ _ _ _.
set nwS2 := fun n => pt_ext_map_data _ _.
have H_eq_n: nwS1 = nwS2.
rewrite /nwS1 /nwS2 /=.
apply functional_extensionality => n.
rewrite /update /=.
case (name_eq_dec _ _) => H_dec //.
by rewrite H_dec tot_map_name_inv_inverse.
by rewrite H_eq_n.
-
left.
rewrite /pt_ext_map_onet /=.
set l := map2snd _ _.
have H_nd: NoDup (map (fun nm => fst nm) (filterMap pt_map_name_msg l)).
rewrite /pt_map_name_msg /=.
rewrite /l {l}.
apply NoDup_map_snd_fst.
apply (@nodup_pt_map _ _ _ _ _ _ _ msg_fail); first exact: in_map2snd_snd.
apply NoDup_map2snd.
apply NoDup_remove_all.
exact: no_dup_nodes.
move => nm nm' H_in H_in'.
by rewrite (pt_map_in_snd _ _ _ _ pt_fail_msg_fst_snd H_in) (pt_map_in_snd _ _ _ _ pt_fail_msg_fst_snd H_in').
exists [].
apply: StepOrderedFailure_fail => //.
*
exact: not_in_failed_not_in.
*
rewrite /=.
rewrite /l collate_pt_map_eq /pt_map_name_msg.
by rewrite (NoDup_Permutation_collate_eq _ _ _ _ _ _ _ H_nd (pt_map_map_pair_eq msg_fail h failed pt_fail_msg_fst_snd)).

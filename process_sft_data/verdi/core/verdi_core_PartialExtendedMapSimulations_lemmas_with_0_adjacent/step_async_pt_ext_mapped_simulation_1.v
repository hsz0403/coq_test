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

Theorem step_async_pt_ext_mapped_simulation_1 : forall net net' tr, @step_async _ multi_fst net net' tr -> (exists tr, @step_async _ multi_snd (pt_ext_map_net net) (pt_ext_map_net net') tr) \/ pt_ext_map_net net' = pt_ext_map_net net.
Proof using name_map_bijective multi_map_congr.
move => net net' tr.
case => {net net' tr}.
-
move => net net' p ms ms' out d l H_eq H_hnd H_eq'.
destruct (pt_map_packet p) eqn:?.
left.
rewrite H_eq' /= /pt_ext_map_net /=.
have H_eq_dst: tot_map_name (pDst p) = pDst p0.
case: p H_eq H_hnd H_eq' Heqo => /= src dst m H_eq H_hnd H_eq'.
case (pt_map_msg m) => //= m' H_m.
by inversion H_m.
destruct (net_handlers (pDst p0) (pSrc p0) (pBody p0) (pt_ext_map_data (nwState net (pDst p)) (pDst p))) eqn:?.
destruct p1 as [out' d'].
exists [(pDst p0, inr out')].
apply StepAsync_deliver with (xs := filterMap pt_map_packet ms) (ys := filterMap pt_map_packet ms') (d0 := pt_ext_map_data d (pDst p)) (l1 := filterMap pt_map_name_msg l).
*
rewrite /= H_eq filterMap_app /=.
case H_p: (pt_map_packet _) => [p1|]; last by rewrite H_p in Heqo.
by rewrite H_p in Heqo; injection Heqo => H_eq_p; rewrite H_eq_p.
*
rewrite /=.
rewrite -{2}H_eq_dst tot_map_name_inv_inverse.
case: p H_eq H_hnd H_eq' Heqo H_eq_dst Heqp1 => /= src dst mg H_eq H_hnd H_eq'.
case H_m: (pt_map_msg mg) => [mg'|] //.
case: p0 H_eq' => src' dst' m0 H_eq' H_eq_p.
inversion H_eq_p; subst.
move => H_eq_dst H_eq_n {H_eq_p H_eq_dst}.
simpl in *.
have H_q := @pt_ext_net_handlers_some _ _ _ _ _ _ _ multi_map_congr dst src mg (nwState net dst) _ _ _ _ H_m H_eq_n.
rewrite /pt_ext_mapped_net_handlers in H_q.
rewrite H_hnd in H_q.
find_inversion.
by rewrite tot_map_name_inv_inverse.
*
rewrite /= /pt_ext_map_net /= 2!filterMap_app.
rewrite (filterMap_pt_map_packet_map_eq_some _ _ Heqo).
by rewrite (pt_ext_map_update_eq_some _ _ _ Heqo).
right.
rewrite H_eq' /= {H_eq'}.
rewrite /pt_ext_map_net /=.
case: p H_eq H_hnd Heqo => /= src dst m H_eq H_hnd.
case H_m: (pt_map_msg _) => [m'|] // H_eq' {H_eq'}.
rewrite 2!filterMap_app H_eq filterMap_app /=.
case H_m': (pt_map_msg _) => [m'|]; first by rewrite H_m' in H_m.
have [H_d H_l] := pt_ext_net_handlers_none _ _ _ _ H_m H_hnd.
rewrite (filterMap_pt_map_name_msg_empty_eq _ dst H_l) /=.
set nwS1 := fun _ => _.
set nwS2 := fun _ => _.
have H_eq_s: nwS1 = nwS2.
rewrite /nwS1 /nwS2 /=.
apply functional_extensionality => n.
rewrite /update /=.
case name_eq_dec => H_dec //.
by rewrite H_dec H_d.
by rewrite H_eq_s.
-
move => h net net' out inp d l H_hnd H_eq.
destruct (pt_ext_map_input inp h (nwState net h)) eqn:?.
left.
destruct (input_handlers (tot_map_name h) i (pt_ext_map_data (nwState net h) h)) eqn:?.
destruct p as [out' d'].
exists [(tot_map_name h, inl i); (tot_map_name h, inr out')].
apply (@StepAsync_input _ _ _ _ _ _ _ (pt_ext_map_data d h) (filterMap pt_map_name_msg l)).
rewrite /=.
have H_q := @pt_ext_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h inp (nwState net h) _ _ _ _ Heqo Heqp.
rewrite /pt_ext_mapped_input_handlers /= in H_q.
rewrite H_hnd in H_q.
find_inversion.
by rewrite tot_map_name_inv_inverse.
rewrite /= H_eq /= /pt_ext_map_net /= filterMap_app filterMap_pt_map_packet_map_eq.
by rewrite -pt_ext_map_update_eq.
right.
rewrite H_eq /pt_ext_map_net /=.
have [H_d H_l] := pt_ext_input_handlers_none _ _ _ Heqo H_hnd.
rewrite filterMap_app.
rewrite (filterMap_pt_map_name_msg_empty_eq _ h H_l) /=.
set nwS1 := fun _ => _.
set nwS2 := fun _ => _.
have H_eq_s: nwS1 = nwS2.
rewrite /nwS1 /nwS2 /=.
apply functional_extensionality => n.
rewrite /update /=.
case name_eq_dec => H_dec //.
by rewrite H_dec H_d.
by rewrite H_eq_s.

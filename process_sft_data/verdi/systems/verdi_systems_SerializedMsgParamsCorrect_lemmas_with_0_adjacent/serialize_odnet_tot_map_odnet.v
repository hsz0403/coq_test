Require Import StructTact.Util.
Require Import Verdi.Verdi.
Require Import FunctionalExtensionality.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Cheerios.Cheerios.
Require Import Verdi.SerializedMsgParams.
Require Import Verdi.Ssrexport.
Section SerializedMsgCorrect.
Context {orig_base_params : BaseParams}.
Context {orig_multi_params : MultiParams orig_base_params}.
Context {orig_failure_params : FailureParams orig_multi_params}.
Context {orig_name_overlay_params : NameOverlayParams orig_multi_params}.
Context {orig_fail_msg_params : FailMsgParams orig_multi_params}.
Context {orig_new_msg_params : NewMsgParams orig_multi_params}.
Context {orig_msg_serializer : Serializer msg}.
Definition serialize_packet p := @mkPacket _ serialized_multi_params (@pSrc _ orig_multi_params p) (pDst p) (serialize_top (serialize (pBody p))).
Definition serialize_net (net : @network _ orig_multi_params) : (@network _ serialized_multi_params) := @mkNetwork _ serialized_multi_params (map serialize_packet (nwPackets net)) net.(nwState).
Definition serialize_onet (net : @ordered_network _ orig_multi_params) : (@ordered_network _ serialized_multi_params) := @mkONetwork _ serialized_multi_params (fun src dst => map (fun v => serialize_top (serialize v)) (net.(onwPackets) src dst)) net.(onwState).
Definition serialize_odnet (net : @ordered_dynamic_network _ orig_multi_params) : (@ordered_dynamic_network _ serialized_multi_params) := @mkODNetwork _ serialized_multi_params net.(odnwNodes) (fun src dst => map (fun v => serialize_top (serialize v)) (net.(odnwPackets) src dst)) net.(odnwState).
Instance orig_multi_params_name_tot_map : MultiParamsNameTotalMap orig_multi_params serialized_multi_params := { tot_map_name := id ; tot_map_name_inv := id }.
Instance orig_multi_params_name_tot_map_bijective : MultiParamsNameTotalMapBijective orig_multi_params_name_tot_map := { tot_map_name_inv_inverse := fun _ => eq_refl ; tot_map_name_inverse_inv := fun _ => eq_refl }.
Instance orig_base_params_tot_map : BaseParamsTotalMap orig_base_params serialized_base_params := { tot_map_data := id; tot_map_input := id; tot_map_output := id }.
Instance orig_multi_params_tot_msg_map : MultiParamsMsgTotalMap orig_multi_params serialized_multi_params := { tot_map_msg := fun v => serialize_top (serialize v) }.
Instance orig_failure_params_tot_map_congruency : FailureParamsTotalMapCongruency orig_failure_params serialized_failure_params orig_base_params_tot_map := { tot_reboot_eq := fun _ => eq_refl }.
Instance orig_multi_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency orig_name_overlay_params serialized_name_overlay_params orig_multi_params_name_tot_map := { tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H) }.
Instance orig_multi_fail_msg_params_tot_map_congruency : FailMsgParamsTotalMapCongruency orig_fail_msg_params serialized_fail_msg_params orig_multi_params_tot_msg_map := { tot_fail_msg_fst_snd := eq_refl }.
Instance orig_multi_new_msg_params_tot_map_congruency : NewMsgParamsTotalMapCongruency orig_new_msg_params serialized_new_msg_params orig_multi_params_tot_msg_map := { tot_new_msg_fst_snd := eq_refl }.
Program Instance orig_multi_params_map_congruency : MultiParamsTotalMapCongruency orig_base_params_tot_map orig_multi_params_name_tot_map orig_multi_params_tot_msg_map := { tot_init_handlers_eq := fun _ => eq_refl ; tot_net_handlers_eq := _ ; tot_input_handlers_eq := _ }.
Next Obligation.
rewrite /tot_mapped_net_handlers /= /tot_map_name_msgs /= /id /=.
repeat break_let.
rewrite /serialized_net_handlers.
rewrite serialize_deserialize_top_id.
rewrite /serialize_handler_result.
repeat break_let.
find_injection.
rewrite map_id.
set l1 := map _ l.
set l2 := map _ l.
suff H_suff: l1 = l2 by rewrite H_suff.
rewrite /l1 /l2.
clear.
elim: l => //=.
move => p l IH.
rewrite IH /= /serialize_name_msg_tuple /=.
by break_let.
Next Obligation.
rewrite /tot_mapped_input_handlers /=.
repeat break_let.
unfold serialized_input_handlers in *.
rewrite /serialize_handler_result /id /tot_map_name_msgs /tot_map_name /= /id /=.
repeat break_let.
find_injection.
rewrite map_id.
set l1 := map _ l.
set l2 := map _ l.
suff H_suff: l1 = l2 by rewrite H_suff.
rewrite /l1 /l2.
clear.
elim: l => //=.
move => p l IH.
rewrite IH /= /serialize_name_msg_tuple /=.
by break_let.
Definition deserialize_packet (p : @packet _ serialized_multi_params) : option (@packet _ orig_multi_params) := match deserialize_top deserialize (pBody p) with | None => None | Some body => Some (@mkPacket _ orig_multi_params (pSrc p) (pDst p) body) end.
Definition deserialize_net (net: @network _ serialized_multi_params) : (@network _ orig_multi_params) := @mkNetwork _ orig_multi_params (filterMap deserialize_packet (nwPackets net)) net.(nwState).
Definition deserialize_onet (net: @ordered_network _ serialized_multi_params) : (@ordered_network _ orig_multi_params) := @mkONetwork _ orig_multi_params (fun src dst => filterMap (fun m => match deserialize_top deserialize m with Some data => Some data | None => None end) (net.(onwPackets) src dst)) net.(onwState).
Definition deserialize_odnet (net: @ordered_dynamic_network _ serialized_multi_params) : (@ordered_dynamic_network _ orig_multi_params) := @mkODNetwork _ orig_multi_params net.(odnwNodes) (fun src dst => filterMap (fun m => match deserialize_top deserialize m with Some data => Some data | None => None end) (net.(odnwPackets) src dst)) net.(odnwState).
Instance multi_params_orig_name_tot_map : MultiParamsNameTotalMap serialized_multi_params orig_multi_params := { tot_map_name := id ; tot_map_name_inv := id }.
Instance multi_params_orig_name_tot_map_bijective : MultiParamsNameTotalMapBijective multi_params_orig_name_tot_map := { tot_map_name_inv_inverse := fun _ => eq_refl _; tot_map_name_inverse_inv := fun _ => eq_refl _ }.
Instance multi_orig_params_pt_msg_map : MultiParamsMsgPartialMap serialized_multi_params orig_multi_params := { pt_map_msg := fun m => match deserialize_top deserialize m with | Some data => Some data | None => None end }.
Instance multi_orig_base_params_pt_map : BaseParamsPartialMap serialized_base_params orig_base_params := { pt_map_data := id; pt_map_input := fun i => Some i; pt_map_output := fun o => Some o }.
Instance multi_orig_failure_params_pt_map_congruency : FailureParamsPartialMapCongruency serialized_failure_params orig_failure_params multi_orig_base_params_pt_map := { pt_reboot_eq := fun _ => eq_refl _ }.
Instance multi_orig_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency serialized_name_overlay_params orig_name_overlay_params multi_params_orig_name_tot_map := { tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H) }.
Program Instance multi_orig_fail_msg_params_pt_map_congruency : FailMsgParamsPartialMapCongruency serialized_fail_msg_params orig_fail_msg_params multi_orig_params_pt_msg_map := { pt_fail_msg_fst_snd := _ }.
Next Obligation.
by rewrite serialize_deserialize_top_id.
Program Instance multi_orig_new_msg_params_pt_map_congruency : NewMsgParamsPartialMapCongruency serialized_new_msg_params orig_new_msg_params multi_orig_params_pt_msg_map := { pt_new_msg_fst_snd := _ }.
Next Obligation.
by rewrite serialize_deserialize_top_id.
Program Instance multi_orig_params_pt_map_congruency : MultiParamsPartialMapCongruency multi_orig_base_params_pt_map multi_params_orig_name_tot_map multi_orig_params_pt_msg_map := { pt_init_handlers_eq := fun _ => eq_refl ; pt_net_handlers_some := _ ; pt_net_handlers_none := _ ; pt_input_handlers_some := _ ; pt_input_handlers_none := _; }.
Next Obligation.
rewrite /pt_mapped_net_handlers.
repeat break_let.
rewrite /tot_map_name /= /id.
rewrite /pt_map_msg /= in H.
rewrite /net_handlers /= /serialized_net_handlers in Heqp.
move: H Heqp.
case H_m: (deserialize_top deserialize m) => [m0|] => H_eq //.
find_injection.
rewrite /serialize_handler_result in Heqp.
repeat break_let.
find_injection.
set sl2 := filterMap (fun _ => _) _.
set sl1 := filterMap _ _.
have H_eq: sl2 = l0.
rewrite /sl2.
clear.
elim: l0 => //=.
move => o l IH.
by rewrite IH.
have H_eq': sl1 = l1.
rewrite /sl1 /pt_map_name_msg /tot_map_name /id /= /id /serialize_name_msg_tuple.
clear.
elim: l1 => //=.
case => [n m] => /=.
move => l IH.
by rewrite serialize_deserialize_top_id IH.
by rewrite H_eq H_eq'.
Next Obligation.
rewrite /net_handlers /= /serialized_net_handlers /= in H0.
rewrite /pt_map_msg /= in H.
move: H H0.
case H_eq_m: (deserialize_top deserialize m) => [m'|] H_eq H_eq'; first by repeat break_let.
by find_injection.
Next Obligation.
rewrite /pt_mapped_input_handlers.
repeat break_let.
destruct p.
rewrite /tot_map_name /= /id.
rewrite /input_handlers /= /serialized_input_handlers in Heqp.
find_injection.
rewrite /serialize_handler_result in Heqp.
repeat break_let.
find_injection.
set sl2 := filterMap (fun _ => _) _.
set sl1 := filterMap _ _.
have H_eq: sl2 = l0.
rewrite /sl2.
clear.
elim: l0 => //=.
move => o l IH.
by rewrite IH.
have H_eq': sl1 = l1.
rewrite /sl1 /pt_map_name_msg /tot_map_name /id /= /id /serialize_name_msg_tuple.
clear.
elim: l1 => //=.
case => [n m] => /=.
move => l IH.
by rewrite serialize_deserialize_top_id IH.
by rewrite H_eq H_eq'.
End SerializedMsgCorrect.

Lemma serialize_odnet_tot_map_odnet : forall net, serialize_odnet net = tot_map_odnet net.
Proof using.
move => net.
rewrite /tot_map_odnet.
rewrite /tot_map_name /= /id /= map_id.
rewrite /serialize_odnet.
set f := fun _ => match _ with _ => _ end.
by have ->: odnwState net = f by rewrite /f; apply functional_extensionality => n; case: odnwState.

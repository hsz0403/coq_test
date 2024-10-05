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

Corollary step_ordered_pt_ext_mapped_simulation_star_1 : forall net tr, @step_ordered_star _ multi_fst step_ordered_init net tr -> exists tr', @step_ordered_star _ multi_snd step_ordered_init (pt_ext_map_onet net) tr'.
Proof using name_map_bijective multi_map_congr.
move => net tr H_step.
remember step_ordered_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
rewrite H_init.
rewrite /step_ordered_init /= /pt_ext_map_net /=.
rewrite pt_ext_init_handlers_fun_eq.
exists [].
exact: RT1nTBase.
concludes.
rewrite H_init in H_step2 H_step1.
apply step_ordered_pt_ext_mapped_simulation_1 in H.
case: H => H.
move: IHH_step1 => [tr' H_star].
move: H => [tr'' H].
exists (tr' ++ tr'').
have H_trans := refl_trans_1n_trace_trans H_star.
apply: H_trans.
have ->: tr'' = tr'' ++ [] by rewrite -app_nil_end.
apply: (@RT1nTStep _ _ _ _ (pt_ext_map_onet x'')) => //.
exact: RT1nTBase.
move: H => [H_eq H_eq'].
move: IHH_step1 => [tr' H_star].
exists tr'.
by rewrite /pt_ext_map_onet H_eq H_eq'.

Require Import List.
Require Import StructTact.StructTactics.
Require Import Verdi.Net.
Require Import StructTact.Util.
Require Import FunctionalExtensionality.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.Ssrexport.
Set Implicit Arguments.
Class GhostMultiParams `(P : MultiParams) := { ghost_data : Type; ghost_init : ghost_data ; ghost_net_handlers : name -> name -> msg -> (ghost_data * data) -> ghost_data; ghost_input_handlers : name -> input -> (ghost_data * data) -> ghost_data }.
Section GhostVars.
Context {base_params : BaseParams}.
Context {multi_params : MultiParams base_params}.
Context {failure_params : FailureParams multi_params}.
Context {ghost_params : GhostMultiParams multi_params}.
Definition refined_net_handlers me src m st := let '(out, st', ps) := net_handlers me src m (snd st) in (out, (ghost_net_handlers me src m st, st'), ps).
Definition refined_input_handlers me inp st := let '(out, st', ps) := input_handlers me inp (snd st) in (out, (ghost_input_handlers me inp st, st'), ps).
Definition refined_init_handlers (n : name) : ghost_data * data := (ghost_init, init_handlers n).
Definition refined_reboot (st : ghost_data * data) := (fst st , reboot (snd st)).
Instance refined_base_params : BaseParams := { data := (ghost_data * data)%type ; input := input ; output := output }.
Instance refined_multi_params : MultiParams _ := { name := name ; msg := msg ; msg_eq_dec := msg_eq_dec ; name_eq_dec := name_eq_dec ; nodes := nodes ; all_names_nodes := all_names_nodes ; no_dup_nodes := no_dup_nodes ; init_handlers := refined_init_handlers; net_handlers := refined_net_handlers ; input_handlers := refined_input_handlers }.
Instance refined_failure_params : FailureParams _ := { reboot := refined_reboot }.
Definition deghost_packet p := @mkPacket _ multi_params (@pSrc _ refined_multi_params p) (pDst p) (pBody p).
Definition deghost (net : @network _ refined_multi_params) : (@network _ multi_params).
refine (@mkNetwork _ multi_params (map deghost_packet (nwPackets net)) _ ).
intros.
destruct net.
concludes.
destruct nwState.
auto.
Defined.
Arguments deghost_packet /_.
Definition deghost_prop I (failed_net : list name * network) : Prop := I ((fst failed_net), deghost (snd failed_net)).
Instance refined_base_params_tot_map : BaseParamsTotalMap refined_base_params base_params := { tot_map_data := snd ; tot_map_input := id ; tot_map_output := id }.
Instance refined_multi_params_name_tot_map : MultiParamsNameTotalMap refined_multi_params multi_params := { tot_map_name := id ; tot_map_name_inv := id }.
Instance refined_multi_params_name_tot_map_bijective : MultiParamsNameTotalMapBijective refined_multi_params_name_tot_map := { tot_map_name_inv_inverse := fun _ => eq_refl ; tot_map_name_inverse_inv := fun _ => eq_refl }.
Instance refined_multi_params_tot_msg_map : MultiParamsMsgTotalMap refined_multi_params multi_params := { tot_map_msg := id }.
Program Instance refined_multi_params_map_congruency : MultiParamsTotalMapCongruency refined_base_params_tot_map refined_multi_params_name_tot_map refined_multi_params_tot_msg_map := { tot_init_handlers_eq := fun _ => eq_refl ; tot_net_handlers_eq := _ ; tot_input_handlers_eq := _ }.
Next Obligation.
rewrite /tot_mapped_net_handlers /= /refined_net_handlers /= /tot_map_name_msgs /= /id /=.
repeat break_let.
find_inversion.
by rewrite /= -/id map_id map_fst_snd_id.
Next Obligation.
rewrite /tot_mapped_input_handlers /=.
repeat break_let.
unfold refined_input_handlers in *.
repeat break_let.
find_inversion.
by rewrite /id /= map_id /tot_map_name_msgs /= /id /= map_fst_snd_id.
Instance refined_failure_params_map_congruency : FailureParamsTotalMapCongruency refined_failure_params failure_params refined_base_params_tot_map := { tot_reboot_eq := fun _ => eq_refl }.
Definition ghost_packet p := @mkPacket _ refined_multi_params (@pSrc _ multi_params p) (pDst p) (pBody p).
Definition reghost (net : @network _ multi_params) : @network _ refined_multi_params.
refine (@mkNetwork _ refined_multi_params (map ghost_packet (nwPackets net)) _ ).
intros.
destruct net.
concludes.
exact (ghost_init, nwState).
Defined.
Arguments ghost_packet /_.
End GhostVars.
Class MsgGhostMultiParams `(P : MultiParams) := { ghost_msg : Type; ghost_msg_eq_dec : forall x y : ghost_msg, {x = y} + {x <> y} ; ghost_msg_default : ghost_msg ; write_ghost_msg : name -> data -> ghost_msg }.
Section MsgGhostVars.
Context {base_params : BaseParams}.
Context {multi_params : MultiParams base_params}.
Context {failure_params : FailureParams multi_params}.
Context {msg_ghost_params : MsgGhostMultiParams multi_params}.
Definition add_ghost_msg (me : name) (st : data) (ps : list (name * msg)) : list (name * (ghost_msg * msg)) := map (fun m => (fst m, (write_ghost_msg me st, snd m))) ps.
Definition mgv_refined_net_handlers me src (m : ghost_msg * msg) st := let '(out, st', ps) := net_handlers me src (snd m) st in (out, st', add_ghost_msg me st' ps).
Definition mgv_refined_input_handlers me inp st := let '(out, st', ps) := input_handlers me inp st in (out, st', add_ghost_msg me st' ps).
Definition mgv_msg_eq_dec : forall x y : ghost_msg * msg, {x = y} + {x <> y}.
Proof using.
intros.
decide equality; auto using msg_eq_dec, ghost_msg_eq_dec.
Instance mgv_refined_base_params : BaseParams := { data := data ; input := input ; output := output }.
Instance mgv_refined_multi_params : MultiParams _ := { name := name ; msg := (ghost_msg * msg) ; msg_eq_dec := mgv_msg_eq_dec ; name_eq_dec := name_eq_dec ; nodes := nodes ; all_names_nodes := all_names_nodes ; no_dup_nodes := no_dup_nodes ; init_handlers := init_handlers; net_handlers := mgv_refined_net_handlers ; input_handlers := mgv_refined_input_handlers }.
Instance mgv_refined_failure_params : FailureParams _ := { reboot := (@reboot base_params multi_params failure_params) }.
Definition mgv_deghost_packet p := @mkPacket _ multi_params (@pSrc _ mgv_refined_multi_params p) (pDst p) (snd (pBody p)).
Definition mgv_deghost (net : @network _ mgv_refined_multi_params) : (@network _ multi_params).
refine (@mkNetwork _ multi_params (map mgv_deghost_packet (nwPackets net)) _ ).
intros.
destruct net.
concludes.
auto.
Defined.
Arguments mgv_deghost_packet /_.
Instance mgv_refined_base_params_tot_map : BaseParamsTotalMap mgv_refined_base_params base_params := { tot_map_data := id ; tot_map_input := id ; tot_map_output := id }.
Instance mgv_refined_multi_params_name_tot_map : MultiParamsNameTotalMap mgv_refined_multi_params multi_params := { tot_map_name := id ; tot_map_name_inv := id ; }.
Instance mgv_refined_multi_params_name_tot_map_bijective : MultiParamsNameTotalMapBijective mgv_refined_multi_params_name_tot_map := { tot_map_name_inv_inverse := fun _ => eq_refl ; tot_map_name_inverse_inv := fun _ => eq_refl }.
Instance mgv_refined_multi_params_tot_map : MultiParamsMsgTotalMap mgv_refined_multi_params multi_params := { tot_map_msg := snd ; }.
Program Instance mgv_refined_multi_params_map_congruency : MultiParamsTotalMapCongruency mgv_refined_base_params_tot_map mgv_refined_multi_params_name_tot_map mgv_refined_multi_params_tot_map := { tot_init_handlers_eq := fun _ => eq_refl ; tot_net_handlers_eq := _ ; tot_input_handlers_eq := _ }.
Next Obligation.
rewrite /tot_mapped_net_handlers /= /mgv_refined_net_handlers /= /tot_map_name_msgs /= /id /=.
repeat break_let.
find_inversion.
rewrite -/id map_id /= /add_ghost_msg /=.
elim l0 => //=.
case => n m' l IH.
find_inversion.
by find_rewrite; find_rewrite.
Next Obligation.
rewrite /tot_mapped_input_handlers /=.
repeat break_let.
rewrite map_id /id /=.
unfold mgv_refined_input_handlers in *.
repeat break_let.
find_inversion.
elim l1 => //=.
case => n m l.
move => IH.
find_inversion.
by find_rewrite; find_rewrite.
Instance mgv_refined_failure_params_map_congruency : FailureParamsTotalMapCongruency mgv_refined_failure_params failure_params mgv_refined_base_params_tot_map := { tot_reboot_eq := fun _ => eq_refl }.
Definition mgv_ghost_packet p := @mkPacket _ mgv_refined_multi_params (@pSrc _ multi_params p) (pDst p) (ghost_msg_default, pBody p).
Definition mgv_reghost (net : @network _ multi_params) : @network _ mgv_refined_multi_params.
refine (@mkNetwork _ mgv_refined_multi_params (map mgv_ghost_packet (nwPackets net)) _ ).
intros.
destruct net.
concludes.
auto.
Defined.
Arguments mgv_ghost_packet /_.
End MsgGhostVars.
Arguments deghost_packet /_ _ _ _.
Arguments ghost_packet /_ _ _ _.
Arguments mgv_deghost_packet /_ _ _ _.
Arguments mgv_ghost_packet /_ _ _ _.

Theorem ghost_simulation_1 : forall net net' failed failed' out, @step_failure _ _ refined_failure_params (failed, net) (failed', net') out -> @step_failure _ _ failure_params (failed, deghost net) (failed', deghost net') out.
Proof using.
move => net net' failed failed' out H_step.
apply step_failure_tot_mapped_simulation_1 in H_step.
rewrite /tot_map_name /tot_map_net /= 2!map_id /id /= in H_step.
rewrite /tot_map_trace_occ /= /id /= in H_step.
rewrite /tot_map_packet /= /id /= in H_step.
rewrite /deghost /=.
rewrite -/id map_id_tr in H_step.
move: H_step.
set fp := fun p : packet => _.
set fp' := fun p : packet => _.
have H_eq: fp = fp' by rewrite /fp /fp'; apply functional_extensionality; case => /= src dst m.
rewrite H_eq {H_eq fp}.
set fs1 := fun n => _.
set fs2 := fun n => _.
set fs1' := fun n => _.
set fs2' := fun n => _.
have H_eq: fs1 = fs1' by rewrite /fs1 /fs1' {fs1 fs1'}; apply functional_extensionality => n; case: net.
rewrite H_eq {H_eq fs1}.
have H_eq: fs2 = fs2' by rewrite /fs2 /fs2' {fs2 fs2'}; apply functional_extensionality => n; case: net'.
by rewrite H_eq {H_eq fs2}.

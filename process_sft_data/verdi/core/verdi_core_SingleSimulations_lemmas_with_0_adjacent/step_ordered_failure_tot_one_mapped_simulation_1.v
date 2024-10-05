Require Import Verdi.Verdi.
Require Import Verdi.DynamicNetLemmas.
Require Import Verdi.Ssrexport.
Set Implicit Arguments.
Class MultiSingleParamsTotalMap (B0 : BaseParams) (P0 : MultiParams B0) (B1 : BaseParams) := { tot_s_map_data : @data B0 -> @data B1 ; tot_s_map_input : name -> @input B0 -> @input B1 ; tot_s_map_output : @output B0 -> @output B1 ; tot_s_map_msg : name -> name -> msg -> @input B1 }.
Class MultiSingleParamsTotalMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : MultiParams B0) (P1 : SingleParams B1) (M : MultiSingleParamsTotalMap P0 B1) (me : name) : Prop := { tot_s_init_handlers_eq : tot_s_map_data (init_handlers me) = init_handler ; tot_s_input_handlers_eq : forall inp st out st' ps out' st'', input_handlers me inp st = (out, st', ps) -> input_handler (tot_s_map_input me inp) (tot_s_map_data st) = (out', st'') -> map tot_s_map_output out = out' /\ tot_s_map_data st' = st'' }.
Section SingleSimulations.
Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {multi : MultiParams base_fst}.
Context {overlay : NameOverlayParams multi}.
Context {fail_msg : FailMsgParams multi}.
Context {single : SingleParams base_snd}.
Context {tot_map : MultiSingleParamsTotalMap multi base_snd}.
Context {me : name} {map_congr : MultiSingleParamsTotalMapCongruency single tot_map me}.
Definition step_ordered_failure_tot_s_net_handlers_eq := forall net failed tr src m ms out st' ps out' st'', step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> onwPackets net src me = m :: ms -> ~ In me failed -> net_handlers me src m (onwState net me) = (out, st', ps) -> input_handler (tot_s_map_msg me src m) (tot_s_map_data (onwState net me)) = (out', st'') -> map tot_s_map_output out = out' /\ tot_s_map_data st' = st''.
Context {new_msg : NewMsgParams multi}.
Definition step_ordered_dynamic_failure_tot_s_net_handlers_eq := forall net failed tr src m ms d out st' ps out' st'', step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> odnwPackets net src me = m :: ms -> ~ In me failed -> odnwState net me = Some d -> net_handlers me src m d = (out, st', ps) -> input_handler (tot_s_map_msg me src m) (tot_s_map_data d) = (out', st'') -> map tot_s_map_output out = out' /\ tot_s_map_data st' = st''.
End SingleSimulations.

Theorem step_ordered_failure_tot_one_mapped_simulation_1 : step_ordered_failure_tot_s_net_handlers_eq -> forall net net' failed failed' tr tr', step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> step_ordered_failure (failed, net) (failed', net') tr' -> net.(onwState) me = net'.(onwState) me \/ exists tr'', @step_s _ single (tot_s_map_data (net.(onwState) me)) (tot_s_map_data (net'.(onwState) me)) tr''.
Proof using map_congr.
move => H_net_eq net net' failed failed' tr tr' H_star H_step.
invcs H_step.
-
rewrite /update.
break_if; last by left.
right.
subst_max.
destruct (input_handler (tot_s_map_msg me from m) (tot_s_map_data (onwState net me))) eqn:?.
have H_eq := H_net_eq _ _ _ _ _ _ _ _ _ _ _ H_star H3 H4 H5 Heqp.
break_and.
exists (inl (tot_s_map_msg me from m) :: (map inr l0)).
apply: SST_deliver => //=.
by rewrite Heqp H0.
-
rewrite /update.
break_if; last by left.
right.
subst_max.
destruct (input_handler (tot_s_map_input me inp) (tot_s_map_data (onwState net me))) eqn:?.
have H_eq_inp := @tot_s_input_handlers_eq _ _ _ _ _ _ map_congr _ _ _ _ _ _ _ H4 Heqp.
break_and.
exists (inl (tot_s_map_input me inp) :: map inr l0).
apply: SST_deliver => //=.
by rewrite Heqp H0.
-
by left.

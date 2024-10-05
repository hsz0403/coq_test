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

Lemma step_ordered_failure_tot_one_mapped_simulation_star_1 : step_ordered_failure_tot_s_net_handlers_eq -> forall net failed tr, step_ordered_failure_star step_ordered_failure_init (failed, net) tr -> exists tr', @step_s_star _ single init_handler (tot_s_map_data (net.(onwState) me)) tr'.
Proof using map_congr.
move => H_net_eq net failed tr H_st.
have ->: net = snd (failed, net) by [].
remember step_ordered_failure_init as y in H_st.
move: Heqy.
induction H_st using refl_trans_1n_trace_n1_ind => /= H_init.
rewrite H_init /=.
exists [].
rewrite tot_s_init_handlers_eq.
exact: RT1nTBase.
concludes.
rewrite H_init {H_init x} in H_st1 H_st2.
case: x' H IHH_st1 H_st1 => failed' net'.
case: x'' H_st2 => failed'' net''.
rewrite /=.
move => H_step2 H IHH_step1 H_step1.
have [tr' H_star] := IHH_step1.
have H_st := step_ordered_failure_tot_one_mapped_simulation_1 H_net_eq H_step1 H.
case: H_st => H_st; first by rewrite -H_st; exists tr'.
have [tr'' H_st'] := H_st.
exists (tr' ++ tr'').
apply: (refl_trans_1n_trace_trans H_star).
have ->: tr'' = tr'' ++ [] by rewrite -app_nil_end.
apply RT1nTStep with (x' := (tot_s_map_data (onwState net'' me))) => //.
exact: RT1nTBase.

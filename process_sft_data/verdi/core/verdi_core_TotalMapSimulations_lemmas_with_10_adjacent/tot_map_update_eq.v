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

Lemma tot_map_name_injective : forall n n', tot_map_name n = tot_map_name n' -> n = n'.
Proof using MB.
move => n n'.
case (name_eq_dec n n') => H_dec //.
move => H_eq.
case: H_dec.
Admitted.

Corollary tot_map_update_packet_eq : forall f p d, (fun n : name => tot_map_data (update name_eq_dec f (pDst p) d (tot_map_name_inv n))) = (update name_eq_dec (fun n : name => tot_map_data (f (tot_map_name_inv n))) (pDst (tot_map_packet p)) (tot_map_data d)).
Proof using name_map_bijective.
move => f.
case => src dst m d.
Admitted.

Lemma tot_map_packet_map_eq : forall l h, map tot_map_packet (map (fun m : name * msg => {| pSrc := h; pDst := fst m; pBody := snd m |}) l) = map (fun m : name * msg => {| pSrc := tot_map_name h; pDst := fst m; pBody := snd m |}) (tot_map_name_msgs l).
Proof using.
elim => //=.
case => /= n m' l IH h.
Admitted.

Lemma tot_init_handlers_fun_eq : init_handlers = fun n : name => tot_map_data (init_handlers (tot_map_name_inv n)).
Proof using name_map_bijective multi_map_congr msg_map.
apply functional_extensionality => n.
Admitted.

Lemma tot_map_trace_occ_inv : forall tr n ol, map tot_map_trace_occ tr = [(n, inr ol)] -> exists n', exists lo, tr = [(n', inr lo)] /\ tot_map_name n' = n /\ map tot_map_output lo = ol.
Proof using.
case => //=.
case.
move => n ol tr n' lo H_eq.
case: tr H_eq => //=.
case: ol => //=.
move => out H_eq.
exists n; exists out.
split => //.
Admitted.

Lemma tot_map_trace_occ_in_inv : forall tr h inp out, map tot_map_trace_occ tr = [(h, inl inp); (h, inr out)] -> exists h', exists inp', exists out', tr = [(h', inl inp'); (h', inr out')] /\ tot_map_name h' = h /\ map tot_map_output out' = out /\ tot_map_input inp' = inp.
Proof using name_map_bijective.
case => //=.
case.
move => h.
case => //.
move => inp.
case => //.
case.
move => h'.
case => //.
move => out.
case => //=.
move => h0.
move => inp' out' H_eq.
inversion H_eq.
find_apply_lem_hyp tot_map_name_injective.
repeat find_rewrite.
Admitted.

Theorem step_async_tot_mapped_simulation_1 : forall net net' tr, @step_async _ multi_fst net net' tr -> @step_async _ multi_snd (tot_map_net net) (tot_map_net net') (map tot_map_trace_occ tr).
Proof using name_map_bijective multi_map_congr.
move => net net' tr.
case => {net net' tr}.
-
move => net net' p ms ms' out d l H_eq H_hnd H_eq'.
rewrite /tot_map_trace_occ /=.
have ->: tot_map_name (pDst p) = pDst (tot_map_packet p) by case: p H_eq H_hnd H_eq' => src dst m H_eq H_hnd H_eq'.
apply (@StepAsync_deliver _ _ _ _ _ (map tot_map_packet ms) (map tot_map_packet ms') (map tot_map_output out) (tot_map_data d) (tot_map_name_msgs l)).
*
by rewrite /tot_map_net /= H_eq /= map_app.
*
rewrite /=.
case: p H_eq H_hnd H_eq' => /= src dst m H_eq H_hnd H_eq'.
have H_q := tot_net_handlers_eq dst src m (nwState net dst).
rewrite /tot_mapped_net_handlers in H_q.
rewrite H_hnd in H_q.
rewrite H_q.
by rewrite tot_map_name_inv_inverse.
*
rewrite /= H_eq' /= /tot_map_net /=.
rewrite -tot_map_update_packet_eq.
rewrite 2!map_app.
destruct p.
by rewrite tot_map_packet_map_eq.
-
move => h net net' out inp d l H_hnd H_eq.
apply (@StepAsync_input _ _ _ _ _ _ _ (tot_map_data d) (tot_map_name_msgs l)).
rewrite /=.
have H_q := tot_input_handlers_eq h inp (nwState net h).
rewrite /tot_mapped_input_handlers /= in H_q.
rewrite H_hnd in H_q.
rewrite H_q.
by rewrite tot_map_name_inv_inverse.
rewrite /= H_eq /= /tot_map_net /=.
Admitted.

Corollary step_async_tot_mapped_simulation_star_1 : forall net tr, @step_async_star _ multi_fst step_async_init net tr -> @step_async_star _ multi_snd step_async_init (tot_map_net net) (map tot_map_trace_occ tr).
Proof using name_map_bijective multi_map_congr.
move => net tr H_step.
remember step_async_init as y in *.
move: Heqy.
induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
rewrite H_init /step_async_init /= /tot_map_net /=.
rewrite tot_init_handlers_fun_eq.
exact: RT1nTBase.
concludes.
repeat find_rewrite.
find_apply_lem_hyp step_async_tot_mapped_simulation_1.
rewrite map_app.
match goal with | H : step_async_star _ _ _ |- _ => apply: (refl_trans_1n_trace_trans H) end.
rewrite (app_nil_end (map _ _)).
apply: (@RT1nTStep _ _ _ _ (tot_map_net x'')) => //.
Admitted.

Theorem step_async_tot_mapped_simulation_2 : forall net net' out mnet mout, @step_async _ multi_snd net net' out -> tot_map_net mnet = net -> map tot_map_trace_occ mout = out -> exists mnet', @step_async _ multi_fst mnet mnet' mout /\ tot_map_net mnet' = net'.
Proof using tot_map_output_injective name_map_bijective multi_map_congr.
move => net net' out mnet mout H_step H_eq H_eq'.
invcs H_step.
-
destruct p.
rewrite /tot_map_net /=.
destruct mnet.
rewrite /=.
match goal with | H : map tot_map_packet _ = _ |- _ => have [pks1 [pks2 [H_eq_pks [H_eq_pks1 H_eq_pks2]]]] := map_eq_inv _ _ _ _ H end.
case: pks2 H_eq_pks H_eq_pks2 => //= p pks2 H_eq_pks H_eq_pks2.
rewrite H_eq_pks.
inversion H_eq_pks2.
case H_hnd': (net_handlers (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p))) => [dout l'].
case: dout H_hnd' => out' d' H_hnd'.
rewrite -H_eq_pks1.
exists {| nwPackets := send_packets (Net.pDst p) l' ++ pks1 ++ pks2 ; nwState := update name_eq_dec nwState (Net.pDst p) d' |}.
split.
*
match goal with | H : _ = map tot_map_trace_occ _ |- _ => have [n' [lo [H_eq_mout [H_eq_n H_eq_lo]]]] := tot_map_trace_occ_inv _ (eq_sym H) end.
rewrite H_eq_mout.
have H_eq_dst: n' = Net.pDst p.
rewrite -(tot_map_name_inv_inverse n') H_eq_n.
destruct p.
find_inversion.
by rewrite tot_map_name_inv_inverse.
rewrite H_eq_dst.
apply (@StepAsync_deliver _ _ _ _ _ pks1 pks2 _ d' l') => //=.
suff H_suff: lo = out' by rewrite H_suff.
have H_eq_hnd := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p)).
rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
repeat break_let.
inversion H_hnd'.
simpl in *.
have H_eq_src: tot_map_name (Net.pSrc p) = pSrc by destruct p; simpl in *; find_inversion.
rewrite H_eq_src /= {H_eq_src} in H_eq_hnd.
have H_eq_body: tot_map_msg (Net.pBody p) = pBody by destruct p; simpl in *; find_inversion.
rewrite H_eq_body in H_eq_hnd.
match goal with | H: net_handlers _ _ _ (tot_map_data (_ (tot_map_name_inv pDst))) = _ |- _ => rewrite -H_eq_n tot_map_name_inv_inverse H_eq_dst in H ; rewrite H in H_eq_hnd end.
find_inversion.
find_apply_lem_hyp map_eq_inv_eq; last exact: tot_map_output_injective.
by symmetry.
*
rewrite /= /update /=.
have H_eq_dst: tot_map_name (Net.pDst p) = pDst by destruct p; find_inversion.
have H_eq_src: tot_map_name (Net.pSrc p) = pSrc by destruct p; find_inversion.
have H_eq_body: tot_map_msg (Net.pBody p) = pBody by destruct p; find_inversion.
rewrite 2!map_app.
have H_eq_hnd := @tot_net_handlers_eq _ _ _ _ _ _ _ multi_map_congr (Net.pDst p) (Net.pSrc p) (Net.pBody p) (nwState (Net.pDst p)).
rewrite /tot_mapped_net_handlers /= in H_eq_hnd.
repeat break_let.
inversion H_hnd'.
rewrite H_eq_dst H_eq_src H_eq_body in H_eq_hnd.
simpl in *.
match goal with | H: net_handlers _ _ _ (tot_map_data (_ (tot_map_name_inv pDst))) = _ |- _ => rewrite -{2}H_eq_dst tot_map_name_inv_inverse in H; rewrite H in H_eq_hnd end.
find_inversion; clean.
set nwP1 := map tot_map_packet _.
set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
set nwS1 := fun _ => _.
set nwS2 := fun _ => _.
have H_eq_nw: nwP1 = nwP2.
rewrite /nwP1 /nwP2.
elim l' => //=.
case => /= n' m' l0 IH.
rewrite IH.
by find_rewrite.
rewrite -H_eq_nw /nwP1 {H_eq_nw nwP1 nwP2}.
have H_eq_sw: nwS1 = nwS2.
rewrite /nwS1 /nwS2.
apply functional_extensionality => n'.
repeat break_if => //.
+
find_reverse_rewrite.
by find_rewrite_lem tot_map_name_inverse_inv.
+
find_rewrite.
by find_rewrite_lem tot_map_name_inv_inverse.
by rewrite H_eq_sw.
-
rewrite /tot_map_net /=.
destruct mnet.
simpl in *.
match goal with | H: _ = map tot_map_trace_occ _ |- _ => have [h' [inp' [out' [H_eq_mout [H_eq_n [H_eq_out H_eq_inp]]]]]] := tot_map_trace_occ_in_inv _ (eq_sym H) end.
have H_q := @tot_input_handlers_eq _ _ _ _ _ _ _ multi_map_congr h' inp' (nwState h').
rewrite /tot_mapped_input_handlers in H_q.
repeat break_let.
rewrite H_eq_n H_eq_inp in H_q.
match goal with | H: input_handlers _ _ (tot_map_data (_ (tot_map_name_inv h))) = _ |- _ => rewrite -{2}H_eq_n tot_map_name_inv_inverse in H; rewrite H in H_q end.
find_inversion.
find_inversion.
exists ({| nwPackets := send_packets h' l0 ++ nwPackets ; nwState := update name_eq_dec nwState h' d0 |}).
split.
*
apply (@StepAsync_input _ _ _ _ _ _ _ d0 l0) => //=.
find_rewrite.
suff H_suff: l1 = out' by rewrite H_suff.
by find_apply_lem_hyp map_eq_inv_eq; last exact: tot_map_output_injective.
*
rewrite /= map_app.
set nwP1 := map tot_map_packet _.
set nwP2 := map (fun _ => _) (tot_map_name_msgs _).
set nwS1 := fun _ => _.
set nwS2 := update _ _ _ _.
have H_eq_nwp: nwP1 = nwP2.
rewrite /nwP1 /nwP2 {nwP1 nwP2}.
elim l0 => //=.
case => /= n m l' IH.
by rewrite IH.
have H_eq_nws: nwS1 = nwS2.
rewrite /nwS1 /nwS2.
rewrite /update /=.
apply functional_extensionality => n.
repeat break_if => //.
+
find_reverse_rewrite.
by find_rewrite_lem tot_map_name_inverse_inv.
+
find_rewrite.
by find_rewrite_lem tot_map_name_inv_inverse.
Admitted.

Lemma not_in_failed_not_in : forall n failed, ~ In n failed -> ~ In (tot_map_name n) (map tot_map_name failed).
Proof using name_map_bijective.
move => n.
elim => //=.
move => n' failed IH H_in H_in'.
case: H_in' => H_in'.
case: H_in.
left.
rewrite -(tot_map_name_inv_inverse n').
rewrite H_in'.
exact: tot_map_name_inv_inverse.
contradict H_in'.
apply: IH.
move => H_in'.
case: H_in.
Admitted.

Lemma in_failed_in : forall n failed, In n failed -> In (tot_map_name n) (map tot_map_name failed).
Proof using.
move => n.
elim => //.
move => n' l IH H_in.
case: H_in => H_in.
rewrite H_in.
by left.
right.
Admitted.

Lemma tot_map_update_eq : forall f d h, (fun n : name => tot_map_data (update name_eq_dec f h d (tot_map_name_inv n))) = update name_eq_dec (fun n : name => tot_map_data (f (tot_map_name_inv n))) (tot_map_name h) (tot_map_data d).
Proof using name_map_bijective.
move => net d h.
apply functional_extensionality => n.
rewrite /update /=.
repeat break_match => //.
-
by find_reverse_rewrite; find_rewrite_lem tot_map_name_inverse_inv.
-
by find_rewrite; find_rewrite_lem tot_map_name_inv_inverse.

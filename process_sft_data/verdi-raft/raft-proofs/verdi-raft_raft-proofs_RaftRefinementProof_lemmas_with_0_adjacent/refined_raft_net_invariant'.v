Require Import FunctionalExtensionality.
Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Set Bullet Behavior "Strict Subproofs".
Section RaftRefinementProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Ltac workhorse := try match goal with | [ |- mkNetwork _ _ = mkNetwork _ _ ] => f_equal end; try match goal with | [ |- (fun _ => _) = (fun _ => _) ] => apply functional_extensionality; intros end; repeat break_match; repeat match goal with | [ H : (_, _) = (_, _) |- _ ] => invc H end; repeat (simpl in *; subst); repeat rewrite map_app; repeat rewrite map_map.
Instance rri : raft_refinement_interface.
Proof.
split.
-
exact refined_raft_net_invariant.
-
exact refined_raft_net_invariant'.
-
exact lift_prop.
-
exact lower_prop.
-
exact deghost_spec.
-
exact simulation_1.
End RaftRefinementProof.
Hint Extern 4 (@BaseParams) => apply raft_refined_base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply raft_refined_multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply raft_refined_failure_params : typeclass_instances.

Theorem refined_raft_net_invariant' : forall P net, refined_raft_net_invariant_init P -> refined_raft_net_invariant_client_request' P -> refined_raft_net_invariant_timeout' P -> refined_raft_net_invariant_append_entries' P -> refined_raft_net_invariant_append_entries_reply' P -> refined_raft_net_invariant_request_vote' P -> refined_raft_net_invariant_request_vote_reply' P -> refined_raft_net_invariant_do_leader' P -> refined_raft_net_invariant_do_generic_server' P -> refined_raft_net_invariant_state_same_packet_subset P -> refined_raft_net_invariant_reboot' P -> refined_raft_intermediate_reachable net -> P net.
Proof using.
intros.
induction H10.
-
intuition.
-
match goal with [H : step_failure _ _ _ |- _ ] => invcs H end.
+
match goal with | [ H : refined_raft_intermediate_reachable _ |- _ ?x ] => assert (refined_raft_intermediate_reachable x) as Hpost by (eapply RRIR_step_failure; eauto; eapply StepFailure_deliver; eauto) end.
unfold refined_net_handlers in *.
simpl in *.
unfold RaftNetHandler, update_elections_data_net in *.
repeat break_let.
repeat find_inversion.
match goal with | [ H : refined_raft_intermediate_reachable ?net, H' : context [net] |- _ ] => match type of H' with | refined_raft_intermediate_reachable _ => move H after H' end end.
assert (refined_raft_intermediate_reachable {| nwPackets := (xs ++ ys) ++ send_packets (pDst p) l2; nwState := update name_eq_dec (nwState net) (pDst p) (update_elections_data_net (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)), r0) |}) by (eapply RRIR_handleMessage; eauto; in_crush).
assert (refined_raft_intermediate_reachable {| nwPackets := ((xs ++ ys) ++ send_packets (pDst p) l2) ++ send_packets (pDst p) l3 ; nwState := update name_eq_dec (nwState {| nwPackets := (xs ++ ys) ++ send_packets (pDst p) l2; nwState := update name_eq_dec (nwState net) (pDst p) (update_elections_data_net (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)), r0) |}) (pDst p) (update_elections_data_net (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)), r1) |}) by (eapply RRIR_doLeader; eauto; [simpl in *; break_if; try congruence; eauto| in_crush]).
eapply_prop refined_raft_net_invariant_do_generic_server'.
eauto.
eapply_prop refined_raft_net_invariant_do_leader'.
eauto.
eapply refined_raft_invariant_handle_message' with (P := P); auto.
eauto.
eauto.
auto.
eauto.
eauto.
eauto using in_app_or.
auto.
eauto.
simpl.
break_if; intuition eauto.
eauto.
simpl.
eapply in_app_or.
auto.
auto.
simpl.
break_if; eauto; congruence.
simpl.
intros.
break_if; subst; repeat rewrite update_same by auto; repeat rewrite update_neq by auto; auto.
simpl.
in_crush.
+
match goal with | [ H : refined_raft_intermediate_reachable _ |- _ ?x ] => assert (refined_raft_intermediate_reachable x) as Hpost by (eapply RRIR_step_failure; eauto; eapply StepFailure_input; eauto) end.
unfold refined_input_handlers in *.
simpl in *.
unfold RaftInputHandler, update_elections_data_input in *.
repeat break_let.
repeat find_inversion.
match goal with | [ H : refined_raft_intermediate_reachable ?net, H' : context [net] |- _ ] => match type of H' with | refined_raft_intermediate_reachable _ => move H after H' end end.
assert (refined_raft_intermediate_reachable {| nwPackets := nwPackets net ++ send_packets h l2; nwState := update name_eq_dec (nwState net) h (update_elections_data_input h inp (nwState net h), r0) |}) by (eapply RRIR_handleInput; eauto; in_crush).
assert (refined_raft_intermediate_reachable {| nwPackets := (nwPackets net ++ send_packets h l2) ++ send_packets h l4 ; nwState := update name_eq_dec (nwState {| nwPackets := nwPackets net ++ send_packets h l2; nwState := update name_eq_dec (nwState net) h (update_elections_data_input h inp (nwState net h), r0) |}) h (update_elections_data_input h inp (nwState net h), r1) |}) by (eapply RRIR_doLeader; eauto; [simpl in *; break_if; try congruence; eauto| in_crush]).
eapply_prop refined_raft_net_invariant_do_generic_server'.
eauto.
eapply_prop refined_raft_net_invariant_do_leader'.
eauto.
eapply refined_raft_invariant_handle_input' with (P := P); auto.
eauto.
all:auto.
all: eauto.
eauto using in_app_or.
simpl.
break_if; intuition eauto.
eauto.
simpl.
eapply in_app_or.
auto.
simpl.
break_if; eauto; congruence.
simpl.
intros.
break_if; subst; repeat rewrite update_same by auto; repeat rewrite update_neq by auto; auto.
simpl.
unfold send_packets.
intros.
in_crush.
+
match goal with | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] => assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) -> In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush) end.
eapply_prop refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|]; eauto.
+
match goal with | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] => assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) -> In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush) end.
eapply_prop refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|]; eauto.
+
auto.
+
eapply_prop refined_raft_net_invariant_reboot'; eauto; intros; simpl in *; repeat break_if; intuition; subst; intuition eauto.
*
econstructor.
eauto.
eapply StepFailure_reboot; eauto.
*
destruct (nwState net h); auto.
-
eapply refined_raft_invariant_handle_input'; eauto.
eapply RRIR_handleInput; eauto.
-
eapply refined_raft_invariant_handle_message'; eauto.
eapply RRIR_handleMessage; eauto.
-
eapply_prop refined_raft_net_invariant_do_leader'; eauto.
eapply RRIR_doLeader; eauto.
-
eapply_prop refined_raft_net_invariant_do_generic_server'; eauto.
eapply RRIR_doGenericServer; eauto.

Require Import Verdi.Verdi.
Require Import Verdi.VarD.
Require Import Verdi.PartialMapSimulations.
Require Import Cheerios.Cheerios.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.Linearizability.
Require Import VerdiRaft.RaftLinearizableProofs.
Require Import VerdiRaft.EndToEndLinearizability.
Require Import Verdi.SerializedMsgParamsCorrect.
Require Import VerdiRaft.VarDRaftSerialized.
Section VarDSerializedCorrect.
Variable n : nat.
Instance raft_params : RaftParams VarD.vard_base_params := raft_params n.
Instance base_params : BaseParams := transformed_base_params n.
Instance multi_params : MultiParams _ := transformed_multi_params n.
Instance failure_params : FailureParams _ := transformed_failure_params n.
End VarDSerializedCorrect.

Lemma correct_filterMap_trace_non_empty_out_input_correct : forall tr, input_correct (filterMap trace_non_empty_out tr) -> input_correct tr.
Proof using.
induction tr; simpl; auto.
destruct a, s; simpl; intro H_inp.
-
assert (H_inp': input_correct (filterMap trace_non_empty_out tr)).
intros client id i0 i1 h h' H_in H_in'.
eapply H_inp; right; eauto.
concludes.
intros client id i0 i1 h h' H_in H_in'.
simpl in *.
break_or_hyp; break_or_hyp.
*
find_injection; find_injection; auto.
*
find_injection.
eapply H_inp; [ idtac | left; eauto ].
right.
eapply filterMap_In; eauto.
simpl; eauto.
*
find_injection.
eapply H_inp; [ left; eauto | idtac ].
right.
eapply filterMap_In; eauto.
simpl; eauto.
*
eapply IHtr; eauto.
-
destruct l.
*
intros client id i0 i1 h h' H_in H_in'.
simpl in *.
break_or_hyp; [ find_inversion | idtac ].
break_or_hyp; [ find_inversion | idtac ].
eapply IHtr; eauto.
*
assert (H_inp': input_correct (filterMap trace_non_empty_out tr)).
intros client id i0 i1 h h' H_in H_in'.
eapply H_inp; right; eauto.
concludes.
intros client id i0 i1 h h' H_in H_in'.
simpl in *.
break_or_hyp; [ find_inversion | idtac ].
break_or_hyp; [ find_inversion | idtac ].
eapply IHtr; eauto.

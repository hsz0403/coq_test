Require Import Verdi.InverseTraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TraceUtil.
Require Import VerdiRaft.OutputImpliesAppliedInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AppliedImpliesInputInterface.
Section AppliedImpliesInputProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {oiai : output_implies_applied_interface}.
Section inner.
Variable client : clientId.
Variable id : nat.
Variable i : input.
Definition aiis_host (net : network) : Prop := exists h e, correct_entry client id i e /\ In e (log (nwState net h)).
Instance aiii : applied_implies_input_interface.
Proof using.
split.
exact applied_implies_input.
End AppliedImpliesInputProof.

Lemma handleMessage_aais : forall client id i net p d' ms e, ~ applied_implies_input_state client id i net -> In p (nwPackets net) -> handleMessage (pSrc p) (pDst p) (pBody p) (nwState net (pDst p)) = (d', ms) -> correct_entry client id i e -> In e (log d') -> False.
Proof using.
intros.
destruct (pBody p) eqn:?; simpl in *; repeat break_let; repeat find_inversion.
-
find_erewrite_lem handleRequestVote_same_log.
eauto using aiis_intro_state.
-
find_erewrite_lem handleRequestVoteReply_same_log.
eauto using aiis_intro_state.
-
find_apply_lem_hyp handleAppendEntries_log.
intuition; find_rewrite.
+
eauto using aiis_intro_state.
+
subst.
eauto using mEntries_intro, aiis_intro_packet.
+
do_in_app.
intuition.
*
eauto using mEntries_intro, aiis_intro_packet.
*
find_apply_lem_hyp removeAfterIndex_in.
eauto using aiis_intro_state.
-
find_erewrite_lem handleAppendEntriesReply_same_log.
eauto using aiis_intro_state.

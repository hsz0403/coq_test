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

Lemma handleMessage_sends_log : forall client id i net p d' ms m es e, In p (nwPackets net) -> handleMessage (pSrc p) (pDst p) (pBody p) (nwState net (pDst p)) = (d', ms) -> correct_entry client id i e -> In m ms -> mEntries (snd m) = Some es -> In e es -> In e (log (nwState net (pDst p))).
Proof using.
intros.
destruct (pBody p) eqn:?; simpl in *; repeat break_let; repeat find_inversion; simpl in *; intuition; subst; simpl in *.
-
exfalso.
eapply handleRequestVote_doesn't_send_AE; eauto using mEntries_some_is_applied_entries.
-
exfalso.
eapply handleAppendEntries_doesn't_send_AE; eauto using mEntries_some_is_applied_entries.
-
exfalso.
eapply handleAppendEntriesReply_doesn't_send_AE; eauto using mEntries_some_is_applied_entries.

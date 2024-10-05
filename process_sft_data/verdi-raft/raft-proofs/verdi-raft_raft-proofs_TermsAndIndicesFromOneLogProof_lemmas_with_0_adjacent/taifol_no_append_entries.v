Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.CurrentTermGtZeroInterface.
Section TermsAndIndicesFromOneLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {ctgzi : current_term_gt_zero_interface}.
Definition terms_and_indices_from_one_log_ind (net : network) : Prop := terms_and_indices_from_one_log net /\ terms_and_indices_from_one_log_nw net.
Instance taifoli : terms_and_indices_from_one_log_interface.
Proof.
split.
-
apply terms_and_indices_from_one_log_ind_invariant.
-
apply terms_and_indices_from_one_log_ind_invariant.
End TermsAndIndicesFromOneLog.

Lemma taifol_no_append_entries : forall ps' net ms p t leaderId prevLogIndex prevLogTerm entries leaderCommit h, (forall (p : packet), In p ps' -> In p (nwPackets net) \/ In p (send_packets h ms)) -> (forall m, In m ms -> ~ is_append_entries (snd m)) -> In p ps' -> pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> terms_and_indices_from_one_log_nw net -> terms_and_indices_from_one entries.
Proof using.
intros.
find_apply_hyp_hyp.
break_or_hyp; eauto.
unfold send_packets in *.
do_in_map.
find_apply_hyp_hyp.
unfold not in *.
find_false.
subst.
simpl in *.
repeat find_rewrite.
eauto 10.

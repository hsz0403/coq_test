Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Section LastAppliedCommitIndexMatching.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lmi : log_matching_interface}.
Context {smsi : state_machine_safety_interface}.
Context {misi : max_index_sanity_interface}.
Instance lacimi : lastApplied_commitIndex_match_interface.
split.
-
exact lastApplied_commitIndex_match_invariant.
-
exact commitIndex_lastApplied_match_invariant.
-
exact lastApplied_lastApplied_match_invariant.
Defined.
End LastAppliedCommitIndexMatching.

Instance lacimi : lastApplied_commitIndex_match_interface.
split.
-
exact lastApplied_commitIndex_match_invariant.
-
exact commitIndex_lastApplied_match_invariant.
-
exact lastApplied_lastApplied_match_invariant.

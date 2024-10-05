Require Import Undecidability.TM.TM.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
From Undecidability.L Require Import L Seval LM_heap_def LM_heap_correct.
Require Import Undecidability.TM.L.HeapInterpreter.M_LHeapInterpreter.
-
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.
Definition eva_LM_lin sigma := exists tau, evaluates step sigma tau.
Require Import Undecidability.L.Functions.Encoding Undecidability.L.Functions.Eval Undecidability.L.Tactics.LTactics.
Import L_Notations.

Lemma LM_halting_LM_halting : HaltLclosed ⪯ eva_LM_lin.
Proof.
eexists (fun '(exist s _ ) => _).
intros [s].
unfold HaltLclosed.
cbn.
setoid_rewrite <- eval_iff.
now eapply red_haltL_to_LM_Lin.

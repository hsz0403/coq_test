Require Import Undecidability.TM.TM.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
From Undecidability.L Require Import L Seval LM_heap_def LM_heap_correct.
Require Import Undecidability.TM.L.HeapInterpreter.M_LHeapInterpreter.
-
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.
Definition eva_LM_lin sigma := exists tau, evaluates step sigma tau.
Require Import Undecidability.L.Functions.Encoding Undecidability.L.Functions.Eval Undecidability.L.Tactics.LTactics.
Import L_Notations.

Lemma HaltL_HaltTM : HaltL ⪯ HaltTM 11.
Proof.
eapply reduces_transitive.
1:exact HaltL_HaltLclosed.
eapply reduces_transitive.
1:exact LM_halting_LM_halting.
eexists (fun x => (existT2 _ _ _ _ _)).
intro.
setoid_rewrite <- halts_eva_LM_lin.
rewrite HaltingProblem.
unfold HaltTM.
cbn.
reflexivity.

Require Import Undecidability.TM.TM.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
From Undecidability.L Require Import L Seval LM_heap_def LM_heap_correct.
Require Import Undecidability.TM.L.HeapInterpreter.M_LHeapInterpreter.
-
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.
Definition eva_LM_lin sigma := exists tau, evaluates step sigma tau.
Require Import Undecidability.L.Functions.Encoding Undecidability.L.Functions.Eval Undecidability.L.Tactics.LTactics.
Import L_Notations.

Lemma halts_eva_LM_lin sigma: halts sigma <-> eva_LM_lin sigma.
Proof.
unfold halts,eva_LM_lin,evaluates,steps,halt_state,terminal.
setoid_rewrite star_def_equiv.
intuition.

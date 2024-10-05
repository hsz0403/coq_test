Require Import Undecidability.TM.TM.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
From Undecidability.L Require Import L Seval LM_heap_def LM_heap_correct.
Require Import Undecidability.TM.L.HeapInterpreter.M_LHeapInterpreter.
-
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.
Definition eva_LM_lin sigma := exists tau, evaluates step sigma tau.
Require Import Undecidability.L.Functions.Encoding Undecidability.L.Functions.Eval Undecidability.L.Tactics.LTactics.
Import L_Notations.

Lemma HaltL_HaltLclosed : HaltL ⪯ HaltLclosed.
Proof.
unshelve eexists.
-
intros s.
exists (Eval (enc s)).
unfold Eval.
Lproc.
-
cbn.
intros s.
unfold HaltL.
split; intros (t & Ht).
+
eapply eval_converges.
edestruct Eval_converges.
eapply H.
eapply eval_iff in Ht.
eauto.
+
setoid_rewrite eval_iff.
eapply eval_converges.
eapply Eval_converges.
eapply Seval.eval_converges.
eauto.

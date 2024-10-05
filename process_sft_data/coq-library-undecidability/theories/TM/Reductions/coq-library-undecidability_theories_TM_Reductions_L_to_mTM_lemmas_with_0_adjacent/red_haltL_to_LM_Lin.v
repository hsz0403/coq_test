Require Import Undecidability.TM.TM.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
From Undecidability.L Require Import L Seval LM_heap_def LM_heap_correct.
Require Import Undecidability.TM.L.HeapInterpreter.M_LHeapInterpreter.
-
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.
Definition eva_LM_lin sigma := exists tau, evaluates step sigma tau.
Require Import Undecidability.L.Functions.Encoding Undecidability.L.Functions.Eval Undecidability.L.Tactics.LTactics.
Import L_Notations.

Lemma red_haltL_to_LM_Lin s: closed s -> HaltL s <-> eva_LM_lin (init s).
Proof.
intros ?.
unfold HaltL, eva_LM_lin.
split.
-
intros (t&R).
eapply eval_iff in R.
eapply completeness in R as (g&Hp&_&R).
2:easy.
eexists.
split.
eassumption.
intros ? H'.
inv H'.
-
intros (?&E).
eapply soundness in E as (?&?&?&?&?&?).
all:eauto.
eexists.
eapply eval_iff.
eauto.

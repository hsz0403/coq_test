From Undecidability Require Import TM.TMEncoding TM.TMinL TM.Util.TM_facts.
From Undecidability.L Require Import Computability.MuRec.
Require Import Undecidability.Synthetic.Definitions.

Lemma TM_eval_halts Σ n (M : TM Σ n) q t q' t' : TM.eval M q t q' t' -> halt M q' = true.
Proof.
induction 1; eauto.

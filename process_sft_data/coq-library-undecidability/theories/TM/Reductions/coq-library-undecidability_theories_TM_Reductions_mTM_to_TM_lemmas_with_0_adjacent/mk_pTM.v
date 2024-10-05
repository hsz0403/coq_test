From Undecidability.TM Require Import Single.StepTM Code.CodeTM TM.
Require Import Undecidability.Synthetic.Definitions.

Lemma mk_pTM n (sig : finType) (m : TM sig n) : pTM sig unit n.
Proof.
unshelve econstructor.
exact m.
exact (fun _ => tt).

Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Synthetic.Definitions.
Definition f (P : stack bool) (A : stack bool) := omap (fun x => pos card_eq x P) A.
Definition g (P : stack bool) (A : list nat) := map (fun n => nth n P ( [], [] )) A.

Lemma tau_itau1 P A : (forall a : nat, a el A -> a < | P |) -> tau1 (g P A) = itau1 P A.
Proof.
intros H.
induction A.
-
reflexivity.
-
cbn.
unfold g in *.
rewrite IHA; firstorder.
now destruct (nth a P ([], [])) eqn:E.

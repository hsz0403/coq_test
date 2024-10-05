Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Synthetic.Definitions.
Definition f (P : stack bool) (A : stack bool) := omap (fun x => pos card_eq x P) A.
Definition g (P : stack bool) (A : list nat) := map (fun n => nth n P ( [], [] )) A.

Lemma itau_tau2 P A : A <<= P -> itau2 P (f P A) = tau2 A.
Proof.
intros H.
induction A as [ | (x,y) ].
-
reflexivity.
-
cbn.
assert ((x, y) el P) as [n E] % (el_pos card_eq) by firstorder.
rewrite E.
cbn.
unfold f in IHA.
rewrite IHA; eauto.
now erewrite pos_nth; eauto.

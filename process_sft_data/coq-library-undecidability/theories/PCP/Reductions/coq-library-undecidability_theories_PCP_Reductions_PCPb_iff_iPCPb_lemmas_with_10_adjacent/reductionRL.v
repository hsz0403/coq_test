Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Synthetic.Definitions.
Definition f (P : stack bool) (A : stack bool) := omap (fun x => pos card_eq x P) A.
Definition g (P : stack bool) (A : list nat) := map (fun n => nth n P ( [], [] )) A.

Lemma itau_tau1 P A : A <<= P -> itau1 P (f P A) = tau1 A.
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
Admitted.

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
Admitted.

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
Admitted.

Lemma tau_itau2 P A : (forall a : nat, a el A -> a < | P |) -> tau2 (g P A) = itau2 P A.
Proof.
intros H.
induction A.
-
reflexivity.
-
cbn.
unfold g in *.
rewrite IHA; firstorder.
Admitted.

Lemma PCPb_iff_iPCPb P : PCPb P <-> iPCPb P.
Proof.
split.
-
intros (A & ? & ? & ?).
exists (f P A).
repeat split.
+
now intros ? (? & ? & ? % pos_length) % in_omap_iff.
+
destruct A; try congruence.
cbn.
assert (c el P) as [n ->] % (el_pos card_eq) by firstorder.
congruence.
+
rewrite itau_tau1, H1, itau_tau2; eauto.
-
intros (A & ? & ? & ?).
exists (g P A).
repeat split.
+
unfold g.
intros ? (? & <- & ?) % in_map_iff.
eapply nth_In; firstorder.
+
destruct A; cbn; congruence.
+
Admitted.

Lemma reductionLR : PCPb ⪯ iPCPb.
Proof.
exists id.
Admitted.

Lemma reductionRL : iPCPb ⪯ PCPb.
Proof.
exists id.
intro x.
now rewrite PCPb_iff_iPCPb.

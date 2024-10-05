Require Import List.
Import ListNotations.
Require Import Undecidability.CFG.CFP.
Require Import Undecidability.CFG.Util.Facts.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Shared.ListAutomation.
Require Import Undecidability.Synthetic.Definitions.
Require Import Arith Lia.
Set Default Proof Using "Type".
Section PCP_CFPP.
Variable P : stack nat.
Definition Sigma := sym P.
Notation "#" := (fresh Sigma).
Definition gamma (A : stack nat) := map (fun '(x,y) => (x, rev y)) A.
Definition palin {X} (A : list X) := A = rev A.
End PCP_CFPP.

Lemma sigma_gamma a A : sigma a (gamma A) = tau1 A ++ a ++ rev (tau2 A).
Proof.
induction A as [ | (x & y) ]; unfold gamma in *; cbn.
-
reflexivity.
-
rewrite IHA.
Admitted.

Lemma tau_eq_iff A a : ~ a el sym A -> tau1 A = tau2 A <-> palin (sigma a (gamma A)).
Proof.
rewrite sigma_gamma.
unfold palin.
simpl_list.
intuition.
-
now rewrite H0.
-
Admitted.

Lemma gamma_invol A : gamma (gamma A) = A.
Proof.
induction A as [ | (x,y) ]; cbn.
-
reflexivity.
-
simpl_list.
Admitted.

Theorem reduction : PCP ⪯ CFPP.
Proof.
exists (fun P => (gamma P, fresh (sym P))).
intros P.
split; intros.
-
destruct H as (A & Hi & He & H).
exists (gamma A).
repeat split.
+
eapply gamma_mono.
now rewrite gamma_invol.
+
destruct A; cbn in *; congruence.
+
eapply tau_eq_iff.
intros F % (sym_mono (P := P)) % fresh_spec; now try eapply F.
eauto.
-
destruct H as (B & Hi & He & H).
exists (gamma B).
repeat split.
+
now eapply gamma_mono.
+
destruct B; cbn in *; congruence.
+
eapply tau_eq_iff with (a := fresh (sym P)).
*
intros F % (sym_mono (P := P)) % fresh_spec.
now eapply F.
now eapply gamma_mono.
*
rewrite gamma_invol.
Admitted.

Lemma gamma_mono A B : A <<= gamma B -> gamma A <<= B.
Proof.
induction A as [ | (x,y) ]; cbn; intros.
-
firstorder.
-
intros ? [ <- | ].
+
assert ( (x, y) el gamma B) by firstorder.
unfold gamma in H0.
eapply in_map_iff in H0 as ((x',y') & ? & ?).
inv H0.
now simpl_list.
+
firstorder.

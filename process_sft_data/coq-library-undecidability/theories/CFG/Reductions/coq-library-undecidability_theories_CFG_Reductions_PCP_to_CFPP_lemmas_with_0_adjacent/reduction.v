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
eassumption.

Require Import List.
Import ListNotations.
Require Import Undecidability.CFG.CFP.
Require Import Undecidability.CFG.Util.Facts.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Shared.ListAutomation.
Require Import Undecidability.Synthetic.Definitions.
Require Import Setoid Morphisms Arith Lia.
Set Default Proof Using "Type".
Section PCP_CFPI.
Variable P : stack nat.
Definition Sigma := sym P.
Notation "#" := (fresh Sigma).
Definition gamma1 (A : stack nat) := map (fun '(x, y) => (x, (x ++ [#] ++ y ++ [#]))) A.
Definition gamma2 (A : stack nat) := map (fun '(x, y) => (y, (x ++ [#] ++ y ++ [#]))) A.
Fixpoint gamma (A : stack nat) := match A with | [] => [] | (x, y) :: A => gamma A ++ x ++ [#] ++ y ++ [#] end.
End PCP_CFPI.

Theorem reduction : PCP ⪯ CFPI.
Proof.
exists (fun P => (gamma1 P P, gamma2 P P, fresh (sym P))).
intros P.
split.
-
intros (A & Hi & He & H).
exists (gamma1 P A), (gamma2 P A).
repeat split.
+
clear He H.
induction A as [ | [] ].
firstorder.
intros ? [ <- | ].
unfold gamma1.
eapply in_map_iff.
exists (l, l0).
firstorder.
firstorder.
+
clear He H.
induction A as [ | [] ].
firstorder.
intros ? [ <- | ].
unfold gamma2.
eapply in_map_iff.
exists (l, l0).
firstorder.
firstorder.
+
destruct A; cbn in *; congruence.
+
destruct A; cbn in *; congruence.
+
now rewrite sigma_gamma1, sigma_gamma2, H.
-
intros (B1 & B2 & (A1 & Hi1 & <-) % gamma1_spec & (A2 & Hi2 & <-) % gamma2_spec & He1 & He2 & H).
rewrite sigma_gamma1, sigma_gamma2 in H.
eapply list_prefix_inv in H as [H1 <- % gamma_inj].
+
exists A1.
firstorder.
destruct A1; cbn in *; firstorder congruence.
+
intros ?.
eapply sym_mono in Hi1.
eapply Hi1 in H0 as ? % fresh_spec.
now apply H2.
+
intros ?.
eapply sym_mono in Hi2.
eapply Hi2 in H0 as ? % fresh_spec.
now apply H2.
+
intros ? % tau1_sym.
eapply sym_mono in Hi1.
eapply Hi1 in H1 as ? % fresh_spec.
now apply H0.
+
intros ? % tau2_sym.
eapply sym_mono in Hi2.
eapply Hi2 in H1 as ? % fresh_spec.
now apply H0.

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

Lemma tau_eq_iff A a : ~ a el sym A -> tau1 A = tau2 A <-> palin (sigma a (gamma A)).
Proof.
rewrite sigma_gamma.
unfold palin.
simpl_list.
intuition.
-
now rewrite H0.
-
eapply list_prefix_inv in H0; firstorder using tau1_sym, tau2_sym.

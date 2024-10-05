Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Set Implicit Arguments.
Unset Strict Implicit.
Definition cards {X : Type} (x: list X) := map (fun a => ([a], [a])) x.
Definition card_eq : forall x y : card bool, {x = y} + {x <> y}.
Proof.
intros.
repeat decide equality.
Defined.
Hint Rewrite (@tau1_app nat) (@tau2_app nat) (@tau1_cards nat) (@tau2_cards nat) : list.
Implicit Types a b : nat.
Implicit Types x y z : string nat.
Implicit Types d e : card nat.
Implicit Types A R P : stack nat.
Fixpoint sym (R : stack nat) := match R with [] => [] | (x, y) :: R => x ++ y ++ sym R end.
Hint Resolve sym_word_l sym_word_R : core.
Coercion sing (n : nat) := [n].
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From Undecidability Require Export PCP.PCP.
From Undecidability.Shared Require Export ListAutomation.
Import ListAutomationNotations.
Local Definition BSRS := list (card bool).
Local Notation "x / y" := (x, y).
Fixpoint L_PCP n : list (BSRS * (string bool * string bool)) := match n with | 0 => [] | S n => L_PCP n ++ [ (C, (x, y)) | (C, x, y) ∈ (L_T BSRS n × L_T (string bool) n × L_T (string bool) n), (x/y) el C ] ++ [ (C, (x ++ u, y ++ v)) | ( (C, (u,v)), x, y) ∈ (L_PCP n × L_T (string bool) n × L_T (string bool) n), (x,y) el C ] end.

Lemma enumerable_PCP : enumerable dPCPb.
Proof.
pose proof enumerable_derivable.
assert (enumerable (X := (stack bool * (string bool * string bool))) (fun '(C, (s, t)) => s = t)).
{
eapply dec_count_enum.
-
eapply decidable_iff.
econstructor.
intros (? & ? & ?).
exact _.
-
eapply enum_enumT.
econstructor.
exact _.
}
unshelve epose proof (enumerable_conj _ _ _ _ H H0).
-
eapply discrete_iff.
econstructor.
exact _.
-
eapply projection in H1 as [f].
exists f.
unfold enumerator in *.
intros x.
rewrite <- H1.
intuition.
+
destruct H2 as [u].
exists (u,u).
eauto.
+
destruct H2 as [[u v] [? ->]].
exists v.
eauto.

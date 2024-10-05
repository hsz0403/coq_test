From Undecidability.Synthetic Require Import DecidabilityFacts SemiDecidabilityFacts EnumerabilityFacts.
From Undecidability Require Import Shared.embed_nat.
Require Import List.
Import ListNotations.
Definition cumulative {X} (L: nat -> list X) := forall n, exists A, L (S n) = L n ++ A.
Hint Extern 0 (cumulative _) => intros ?; cbn; eauto : core.
Definition list_enumerator {X} (L: nat -> list X) (p : X -> Prop) := forall x, p x <-> exists m, In x (L m).
Definition list_enumerable {X} (p : X -> Prop) := exists L, list_enumerator L p.
Definition list_enumerator__T' X f := forall x : X, exists n : nat, In x (f n).
Notation list_enumerator__T f X := (list_enumerator__T' X f).
Definition list_enumerable__T X := exists f : nat -> list X, list_enumerator__T f X.
Definition inf_list_enumerable__T X := { f : nat -> list X | list_enumerator__T f X }.
Section enumerator_list_enumerator.
Variable X : Type.
Variable p : X -> Prop.
Variables (e : nat -> option X).
Let T (n : nat) : list X := match e n with Some x => [x] | None => [] end.
End enumerator_list_enumerator.
Section enumerator_list_enumerator.
Variable X : Type.
Variables (T : nat -> list X).
Let e (n : nat) : option X := let (n, m) := unembed n in nth_error (T n) m.
End enumerator_list_enumerator.
Definition to_cumul {X} (L : nat -> list X) := fix f n := match n with 0 => [] | S n => f n ++ L n end.
Hint Resolve cumul_In In_cumul : core.
Require Import Undecidability.Shared.ListAutomation.
Import ListAutomationNotations.
Notation cumul := (to_cumul).
Section L_list_def.
Context {X : Type}.
Variable (L : nat -> list X).
Fixpoint L_list (n : nat) : list (list X) := match n with | 0 => [ [] ] | S n => L_list n ++ [ x :: L | (x,L) ∈ (cumul L n × L_list n) ] end.
End L_list_def.
Hint Extern 4 => match goal with [H : list_enumerator _ ?p |- ?p _ ] => eapply H end : core.
Definition L_T {X : Type} {f : nat -> list X} {H : list_enumerator__T f X} : nat -> list X.
Proof.
exact (cumul f).
Defined.
Arguments L_T _ {_ _} _, {_ _ _}.
Hint Unfold L_T : core.
Hint Resolve cumul_In : core.
Existing Class list_enumerator__T'.
Definition el_T {X} {f} `{list_enumerator__T f X} : list_enumerator__T L_T X.
Proof.
now eapply cumul_spec__T.
Defined.
Existing Instance enumerator__T_list.
Instance enumerator__T_to_list {X} {f} : list_enumerator__T f X -> enumerator__T (fun n => let (n, m) := unembed n in nth_error (f n) m) X | 100.
Proof.
intros H x.
eapply list_enumerator_to_enumerator in H.
exact H.
Instance enumerator__T_of_list {X} {f} : enumerator__T f X -> list_enumerator__T (fun n => match f n with Some x => [x] | None => [] end) X | 100.
Proof.
intros H x.
eapply enumerator_to_list_enumerator.
eauto.
Existing Class inf_list_enumerable__T.
Instance inf_to_enumerator {X} : forall H : inf_list_enumerable__T X, list_enumerator__T (proj1_sig H) X | 100.
Proof.
intros [? H].
eapply H.
Defined.
Hint Unfold enumerable list_enumerable : core.
Hint Resolve enumerable_list_enumerable list_enumerable_enumerable : core.

Lemma list_enumerator_to_enumerator : forall x, (exists n, e n = Some x) <-> (exists n, In x (T n)).
Proof.
split; intros [k H].
-
unfold e in *.
destruct (unembed k) as (n, m).
exists n.
eapply (nth_error_In _ _ H).
-
unfold e in *.
eapply In_nth_error in H as [m].
exists (embed (k, m)).
now rewrite embedP, H.

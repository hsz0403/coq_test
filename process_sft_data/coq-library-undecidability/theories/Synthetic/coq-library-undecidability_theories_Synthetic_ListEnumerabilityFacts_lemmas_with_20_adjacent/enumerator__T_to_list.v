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
Admitted.

Lemma list_enumerator_enumerator {X} {p : X -> Prop} {T} : list_enumerator T p -> enumerator (fun n => let (n, m) := unembed n in nth_error (T n) m) p.
Proof.
unfold list_enumerator.
intros H x.
rewrite list_enumerator_to_enumerator.
Admitted.

Lemma list_enumerable_enumerable {X} {p : X -> Prop} : list_enumerable p -> enumerable p.
Proof.
intros [T HT].
eexists.
unfold list_enumerator.
intros x.
rewrite list_enumerator_to_enumerator.
Admitted.

Lemma list_enumerable__T_enumerable {X} : list_enumerable__T X -> enumerable__T X.
Proof.
intros [T HT].
eexists.
unfold list_enumerator.
intros x.
rewrite list_enumerator_to_enumerator.
Admitted.

Lemma enum_enumT {X} : enumerable__T X <-> list_enumerable__T X.
Proof.
split.
eapply enumerable__T_list_enumerable.
Admitted.

Lemma to_cumul_cumulative {X} (L : nat -> list X) : cumulative (to_cumul L).
Proof.
Admitted.

Lemma to_cumul_spec {X} (L : nat -> list X) x : (exists n, In x (L n)) <-> exists n, In x (to_cumul L n).
Proof.
split.
-
intros [n H].
exists (S n).
cbn.
eapply in_app_iff.
eauto.
-
intros [n H].
induction n; cbn in *.
+
inversion H.
+
Admitted.

Lemma cumul_In {X} (L : nat -> list X) x n : In x (L n) -> In x (to_cumul L (S n)).
Proof.
intros H.
cbn.
eapply in_app_iff.
Admitted.

Lemma In_cumul {X} (L : nat -> list X) x n : In x (to_cumul L n) -> exists n, In x (L n).
Proof.
intros H.
eapply to_cumul_spec.
Admitted.

Lemma list_enumerator_to_cumul {X} {p : X -> Prop} {L} : list_enumerator L p -> list_enumerator (to_cumul L) p.
Proof.
unfold list_enumerator.
intros.
rewrite H.
Admitted.

Lemma cumul_spec__T {X} {L} : list_enumerator__T L X -> list_enumerator__T (to_cumul L) X.
Proof.
unfold list_enumerator__T.
intros.
Admitted.

Lemma cumul_spec {X} {L} {p : X -> Prop} : list_enumerator L p -> list_enumerator (to_cumul L) p.
Proof.
unfold list_enumerator.
intros.
Admitted.

Lemma L_list_cumulative {X} L : cumulative (@L_list X L).
Proof.
Admitted.

Lemma enumerator__T_list {X} L : list_enumerator__T L X -> list_enumerator__T (L_list L) (list X).
Proof.
intros H l.
induction l.
-
exists 0.
cbn.
eauto.
-
destruct IHl as [n IH].
destruct (cumul_spec__T H a) as [m ?].
exists (1 + n + m).
cbn.
intros.
in_app 2.
in_collect (a,l).
Admitted.

Lemma enumerable_list {X} : list_enumerable__T X -> list_enumerable__T (list X).
Proof.
intros [L H].
eexists.
Admitted.

Lemma enumerable_conj X (p q : X -> Prop) : discrete X -> enumerable p -> enumerable q -> enumerable (fun x => p x /\ q x).
Proof.
intros [] % discrete_iff [Lp] % enumerable_list_enumerable [Lq] % enumerable_list_enumerable.
eapply list_enumerable_enumerable.
exists (fix f n := match n with 0 => [] | S n => f n ++ [ x | x ∈ cumul Lp n, x el cumul Lq n] end).
intros.
split.
+
intros [].
eapply (cumul_spec H) in H1 as [m1].
eapply (cumul_spec H0) in H2 as [m2].
exists (1 + m1 + m2).
cbn.
in_app 2.
in_collect x.
eapply cum_ge'; eauto.
lia.
eapply cum_ge'; eauto.
lia.
+
intros [m].
induction m.
*
inv H1.
*
Admitted.

Lemma projection X Y (p : X * Y -> Prop) : enumerable p -> enumerable (fun x => exists y, p (x,y)).
Proof.
intros [f].
exists (fun n => match f n with Some (x, y) => Some x | None => None end).
intros; split.
-
intros [y ?].
eapply H in H0 as [n].
exists n.
now rewrite H0.
-
intros [n ?].
destruct (f n) as [ [] | ] eqn:E; inv H0.
exists y.
eapply H.
Admitted.

Lemma projection' X Y (p : X * Y -> Prop) : enumerable p -> enumerable (fun y => exists x, p (x,y)).
Proof.
intros [f].
exists (fun n => match f n with Some (x, y) => Some y | None => None end).
intros y; split.
-
intros [x ?].
eapply H in H0 as [n].
exists n.
now rewrite H0.
-
intros [n ?].
destruct (f n) as [ [] | ] eqn:E; inv H0.
exists x.
eapply H.
Admitted.

Definition L_T {X : Type} {f : nat -> list X} {H : list_enumerator__T f X} : nat -> list X.
Proof.
Admitted.

Definition el_T {X} {f} `{list_enumerator__T f X} : list_enumerator__T L_T X.
Proof.
Admitted.

Instance enumerator__T_of_list {X} {f} : enumerator__T f X -> list_enumerator__T (fun n => match f n with Some x => [x] | None => [] end) X | 100.
Proof.
intros H x.
eapply enumerator_to_list_enumerator.
Admitted.

Instance inf_to_enumerator {X} : forall H : inf_list_enumerable__T X, list_enumerator__T (proj1_sig H) X | 100.
Proof.
intros [? H].
Admitted.

Lemma enumerable_enum {X} {p : X -> Prop} : enumerable p <-> list_enumerable p.
Proof.
Admitted.

Instance enumerator__T_to_list {X} {f} : list_enumerator__T f X -> enumerator__T (fun n => let (n, m) := unembed n in nth_error (f n) m) X | 100.
Proof.
intros H x.
eapply list_enumerator_to_enumerator in H.
exact H.

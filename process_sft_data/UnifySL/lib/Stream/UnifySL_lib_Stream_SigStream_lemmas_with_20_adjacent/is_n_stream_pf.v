Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Export Coq.Logic.Classical.
Require Export Coq.Logic.Classical_Prop.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.NatChoice.
Definition stream (A: Type): Type := {h: nat -> option A | forall x y, x < y -> h x = None -> h y = None}.
Definition stream_get {A: Type} (h: stream A) (n: nat) := proj1_sig h n.
Coercion stream_get: stream >-> Funclass.
Tactic Notation "stream_extensionality" ident(x) := match goal with [ |- ?X = ?Y ] => apply stream_extensionality; intro x end.
Definition is_n_stream {A: Type} (n: nat) (h: stream A): Prop := h n = None /\ forall n', n' < n -> h n' <> None.
Definition is_fin_stream {A: Type} (h: stream A): Prop := exists n, h n = None.
Definition is_inf_stream {A: Type} (h: stream A): Prop := forall n, h n <> None.
Definition is_at_least_n_stream {A: Type} (n: nat) (h: stream A): Prop := forall n', n' < n -> h n' <> None.
Definition is_at_most_n_stream {A: Type} (n: nat) (h: stream A): Prop := h n = None.
Definition is_empty_stream {A: Type}: stream A -> Prop := is_n_stream 0.

Lemma stream_sound1: forall {A: Type} (h: stream A) (x y: nat), x <= y -> h x = None -> h y = None.
Proof.
intros ? [h ?] ? ? ?.
destruct H; auto; simpl.
apply (e x (S m)).
Admitted.

Lemma stream_sound2: forall {A: Type} (h: stream A) (x y: nat), x <= y -> (exists a, h y = Some a) -> (exists a, h x = Some a).
Proof.
intros.
pose proof stream_sound1 h x y H.
destruct (h x), (h y), H0; eauto.
specialize (H1 eq_refl).
Admitted.

Lemma stream_extensionality {A: Type}: forall h1 h2: stream A, (forall n, h1 n = h2 n) -> h1 = h2.
Proof.
intros.
destruct h1 as [h1 ?H], h2 as [h2 ?H]; simpl in *.
assert (h1 = h2) by (extensionality n; auto).
subst h2.
assert (H0 = H1) by (apply proof_irrelevance).
subst H1.
Admitted.

Lemma n_stream_inf_stream_conflict {A: Type}: forall (h: stream A) (n: nat), is_n_stream n h -> is_inf_stream h -> False.
Proof.
intros.
destruct H.
Admitted.

Lemma at_most_n_stream_Sn {A: Type}: forall (h: stream A) (n: nat), is_at_most_n_stream (S n) h <-> is_at_most_n_stream n h \/ is_n_stream (S n) h.
Proof.
intros.
split; [intro | intros [? | ?]].
+
destruct (h n) eqn:?H.
-
right.
split; auto.
intros; intro.
rewrite (stream_sound1 h n' n) in H0 by (auto; omega).
congruence.
-
left.
auto.
+
hnf in H |- *.
rewrite (stream_sound1 h n (S n)) by (auto; omega).
auto.
+
Admitted.

Lemma at_most_n_stream_0 {A: Type}: forall (h: stream A), is_at_most_n_stream 0 h <-> is_n_stream 0 h.
Proof.
intros; split; intros.
+
split; auto.
intros; omega.
+
Admitted.

Lemma at_most_n_stream_spec {A: Type}: forall (h: stream A) (n: nat), is_at_most_n_stream n h <-> exists m, m <= n /\ is_n_stream m h.
Proof.
intros.
induction n.
+
rewrite at_most_n_stream_0.
split; intros.
-
exists 0; split; [omega | auto].
-
destruct H as [m [? ?]].
replace m with 0 in H0 by omega.
auto.
+
rewrite at_most_n_stream_Sn.
rewrite IHn.
split; intros.
-
destruct H as [[m [? ?]] | ?].
*
exists m; split; [omega | auto].
*
exists (S n); split; [omega | auto].
-
destruct H as [m [? ?]].
destruct (le_gt_dec m n).
*
left; exists m; split; auto.
*
right.
replace (S n) with m by omega.
Admitted.

Lemma is_fin_stream_spec {A}: forall (h: stream A), is_fin_stream h <-> exists n, is_n_stream n h.
Proof.
intros.
split; intro.
+
destruct H as [n ?].
apply at_most_n_stream_spec in H.
destruct H as [m [? ?]].
exists m; auto.
+
destruct H as [n [? ?]].
Admitted.

Lemma at_most_n_stream_mono {A: Type}: forall (h: stream A) (n m: nat), n <= m -> is_at_most_n_stream n h -> is_at_most_n_stream m h.
Proof.
intros.
rewrite at_most_n_stream_spec in H0 |- *.
destruct H0 as [m0 [? ?]].
exists m0.
Admitted.

Lemma at_most_n_stream_is_fin_stream {A: Type}: forall (h: stream A) (n: nat), is_at_most_n_stream n h -> is_fin_stream h.
Proof.
intros.
rewrite at_most_n_stream_spec in H.
rewrite is_fin_stream_spec.
destruct H as [m [? ?]].
Admitted.

Lemma n_stream_or_inf_stream {A: Type}: forall (h: stream A), (exists n, is_n_stream n h) \/ is_inf_stream h.
Proof.
intros.
destruct (classic (is_fin_stream h)).
+
left.
rewrite is_fin_stream_spec in H.
auto.
+
right.
hnf; intros; intro.
apply H; clear H.
Admitted.

Lemma at_least_n_stream_Sn {A: Type}: forall (h: stream A) (n: nat), is_at_least_n_stream (S n) h <-> is_at_least_n_stream n h /\ ~ is_n_stream n h.
Proof.
intros.
split; [intro | intros [? ?]].
+
split.
-
hnf in H |- *.
intros; apply H; omega.
-
intros [? ?].
exact (H n (le_n _) H0).
+
hnf in H |- *.
intros; intro.
apply H0; clear H0.
split.
-
specialize ((fun HH => H n' HH H2): ~ n' < n).
replace n with n' by omega; auto.
-
Admitted.

Lemma at_least_n_stream_0 {A: Type}: forall (h: stream A), is_at_least_n_stream 0 h <-> True.
Proof.
intros.
split; auto.
intros _.
hnf; intros.
Admitted.

Lemma at_least_n_stream_spec {A: Type}: forall (h: stream A) (n: nat), is_at_least_n_stream n h <-> (exists m, m >= n /\ is_n_stream m h) \/ is_inf_stream h.
Proof.
intros.
induction n.
+
rewrite at_least_n_stream_0.
split; auto; intros _.
destruct (n_stream_or_inf_stream h) as [[m ?] | ?].
-
left; exists m; split; [omega | auto].
-
right; auto.
+
rewrite at_least_n_stream_Sn.
rewrite IHn.
split; intros.
-
destruct H as [[[m [? ?]] | ?] ?].
*
left; exists m; split; [| auto].
destruct (Nat.eq_dec m n); [subst; tauto | omega].
*
right; auto.
-
destruct H as [[m [? ?]] | ?].
*
split.
++
left; exists m; split; [omega | auto].
++
intro.
pose proof (is_n_stream_pf _ _ _ H0 H1).
omega.
*
split.
++
right; auto.
++
intros [? ?].
Admitted.

Lemma is_inf_stream_spec {A}: forall (h: stream A), is_inf_stream h <-> forall n, ~ is_n_stream n h.
Proof.
intros.
split; intro.
+
intros.
intros [? ?].
exact (H _ H0).
+
destruct (n_stream_or_inf_stream h) as [[m ?] | ?]; [| auto].
exfalso.
Admitted.

Lemma at_least_n_stream_mono {A: Type}: forall (h: stream A) (n m: nat), n <= m -> is_at_least_n_stream m h -> is_at_least_n_stream n h.
Proof.
intros.
rewrite at_least_n_stream_spec in H0 |- *.
destruct H0 as [[m0 [? ?]] | ?].
+
left; exists m0.
split; [omega | auto].
+
Admitted.

Lemma inf_stream_is_at_least_n_stream_is_fin_stream {A: Type}: forall (h: stream A) (n: nat), is_inf_stream h -> is_at_least_n_stream n h.
Proof.
intros.
rewrite at_least_n_stream_spec.
Admitted.

Lemma at_most_n_stream_or_at_least_Sn_stream {A: Type}: forall (h: stream A) (n: nat), is_at_most_n_stream n h \/ is_at_least_n_stream (S n) h.
Proof.
intros.
destruct (n_stream_or_inf_stream h) as [[m ?] | ?]; [destruct (lt_dec n m) |].
+
right.
rewrite at_least_n_stream_spec.
left; exists m.
split; [omega | tauto].
+
left.
rewrite at_most_n_stream_spec.
exists m.
split; [omega | tauto].
+
right.
rewrite at_least_n_stream_spec.
Admitted.

Lemma at_most_n_stream_or_at_least_n_stream {A: Type}: forall (h: stream A) (n: nat), is_at_most_n_stream n h \/ is_at_least_n_stream n h.
Proof.
intros.
destruct (at_most_n_stream_or_at_least_Sn_stream h n).
+
left; auto.
+
right.
eapply at_least_n_stream_mono; [| eassumption].
Admitted.

Lemma is_n_stream_pf {A: Type}: forall (h: stream A) (n m: nat), is_n_stream m h -> is_n_stream n h -> n = m.
Proof.
intros ?.
assert (forall n m, n < m -> is_n_stream m h -> is_n_stream n h -> False).
{
intros.
destruct H0, H1.
specialize (H2 n H).
congruence.
}
intros; destruct (lt_eq_lt_dec n m) as [[?H | ?H] | ?H].
+
specialize (H _ _ H2 H0 H1); contradiction.
+
auto.
+
specialize (H _ _ H2 H1 H0); contradiction.

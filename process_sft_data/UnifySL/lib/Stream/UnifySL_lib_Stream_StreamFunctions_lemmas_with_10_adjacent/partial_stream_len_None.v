Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.StrongInduction.
Require Import Logic.lib.Stream.SigStream.
Definition fin_stream {A: Type} (h: list A) : stream A.
exists (fun n => nth_error h n).
intros.
rewrite nth_error_None_iff in H0 |- *.
omega.
Defined.
Definition inf_stream {A: Type} (h: nat -> A) : stream A.
exists (fun n => Some (h n)).
intros.
congruence.
Defined.
Definition empty_stream {A: Type}: stream A := fin_stream nil.
Definition empty_stream_spec {A: Type}: forall n, @empty_stream A n = None.
Proof.
intros.
simpl.
destruct n; auto.
Program Definition stream_map {A B: Type} (f: A -> B) (h: stream A): stream B := fun n => match h n return option B with | Some a => Some (f a) | None => None end.
Next Obligation.
pose proof proj2_sig h x y H.
change (proj1_sig h) with (stream_get h) in H1.
destruct (h x), (h y); try congruence.
specialize (H1 eq_refl); congruence.
Program Definition fstn_stream {A: Type} (n: nat) (h: stream A) : stream A := fun m => if le_lt_dec n m then None else h m.
Next Obligation.
destruct (le_lt_dec n x), (le_lt_dec n y); try congruence.
+
omega.
+
apply (stream_sound1 h x y); auto; omega.
Definition skipn_stream {A: Type} (n: nat) (h: stream A) : stream A.
exists (fun m => h (m + n)).
intros.
revert H0; apply (stream_sound1 h).
omega.
Defined.
Definition partial_stream_len {A: Type} (h: stream A) (n: nat): option nat := match h n with | Some _ => None | None => Some ((fix f (m: nat): nat := match h m with | Some _ => S m | None => match m with | 0 => 0 | S m0 => f m0 end end) n) end.
Program Definition stream_app {A: Type} (h1 h2: stream A): stream A := fun n: nat => match partial_stream_len h1 n return option A with | None => h1 n | Some m => h2 (n - m) end.
Next Obligation.
destruct (partial_stream_len h1 x) eqn:?H.
+
pose proof H1.
apply (partial_stream_len_mono2 h1 x y n) in H1; [| omega].
rewrite H1.
apply (stream_sound1 h2 (x - n) (y - n)); auto.
omega.
+
unfold partial_stream_len in H1.
rewrite H0 in H1.
congruence.
Fixpoint partial_stream_clen {A: Type} (h: nat -> stream A) (n: nat): nat * nat := match n with | 0 => (0, 0) | S n => let (k, m) := partial_stream_clen h n in match h k (S m) with | Some _ => (k, S m) | None => (S k, 0) end end.
Fixpoint partial_stream_clen' {A: Type} (h: nat -> stream A) (n: nat): option (nat * nat) := let (k, m) := partial_stream_clen h n in match n with | 0 => match h k m with | Some _ => Some (k, m) | None => None end | S n => match h k m, partial_stream_clen' h n with | Some _, Some _ => Some (k, m) | _, _ => None end end.
Program Definition stream_capp {A: Type} (h: nat -> stream A): stream A := fun n: nat => match partial_stream_clen' h n return option A with | Some (k, m) => h k m | None => None end.
Next Obligation.
assert (x <= y) by omega; clear H.
rewrite partial_stream_clen'_None_iff in H0 |- *.
induction H1; auto.
clear H0 H1 x.
Opaque partial_stream_clen.
simpl.
Transparent partial_stream_clen.
destruct (partial_stream_clen h (S m)) as [k n].
rewrite IHle.
destruct (h k n); auto.

Lemma fstn_stream_Some {A: Type}: forall n m (h: stream A), m < n -> (fstn_stream n h) m = h m.
Proof.
intros; simpl.
Admitted.

Lemma fstn_stream_None {A: Type}: forall n m (h: stream A), n <= m -> (fstn_stream n h) m = None.
Proof.
intros; simpl.
Admitted.

Lemma fstn_stream_is_n_stream {A: Type}: forall n (h: stream A), is_at_least_n_stream n h -> is_n_stream n (fstn_stream n h).
Proof.
intros.
hnf in H.
split.
+
rewrite fstn_stream_None by auto; auto.
+
intros.
rewrite fstn_stream_Some by omega.
Admitted.

Lemma fstn_stream_eq {A: Type}: forall n (h: stream A), is_at_most_n_stream n h -> fstn_stream n h = h.
Proof.
intros.
hnf in H.
stream_extensionality m.
destruct (lt_dec m n).
+
rewrite fstn_stream_Some by omega; auto.
+
rewrite fstn_stream_None by omega.
symmetry.
Admitted.

Lemma fstn_stream_is_fin_stream {A: Type}: forall n (h: stream A), is_fin_stream (fstn_stream n h).
Proof.
intros.
destruct (at_most_n_stream_or_at_least_Sn_stream h n).
+
rewrite fstn_stream_eq by auto.
eapply at_most_n_stream_is_fin_stream; eauto.
+
eapply at_most_n_stream_is_fin_stream.
apply fstn_stream_is_n_stream.
eapply at_least_n_stream_mono; [| eauto].
Admitted.

Lemma skipn_stream_spec {A: Type}: forall n m (h: stream A), (skipn_stream n h) m = h (m + n).
Proof.
intros; simpl.
Admitted.

Lemma skipn_stream_empty {A: Type}: forall n (h: stream A), is_at_most_n_stream n h -> skipn_stream n h = empty_stream.
Proof.
intros.
stream_extensionality m.
rewrite skipn_stream_spec.
hnf in H.
rewrite (stream_sound1 h n (m + n)) by (auto; omega).
rewrite empty_stream_spec.
Admitted.

Lemma partial_stream_len_mono1: forall {A: Type} (h: stream A) (x y: nat), x <= y -> partial_stream_len h y = None -> partial_stream_len h x = None.
Proof.
intros.
unfold partial_stream_len in *.
destruct (h y) eqn:?H; try congruence.
pose proof (stream_sound2 h x y H) as [? ?]; [eauto |].
Admitted.

Lemma partial_stream_len_mono2: forall {A: Type} (h: stream A) (x y n: nat), x <= y -> partial_stream_len h x = Some n -> partial_stream_len h y = Some n.
Proof.
intros.
unfold partial_stream_len in *.
destruct (h x) eqn:?H; try congruence.
pose proof (stream_sound1 h x y H H1).
inversion H0.
rewrite H2, H4; clear H0.
f_equal.
revert n H4; induction H; intros; auto.
pose proof (stream_sound1 h x m H H1).
specialize (IHle H0 _ H4).
rewrite IHle; clear IHle.
Admitted.

Lemma partial_stream_len_Some {A: Type}: forall (h: stream A) (n m: nat), n <= m -> is_n_stream n h -> partial_stream_len h m = Some n.
Proof.
intros.
unfold partial_stream_len.
destruct H0.
rewrite (stream_sound1 h n m H) by auto.
f_equal.
remember (m - n) as d.
replace m with (d + n) by omega.
clear Heqd H m.
induction d.
+
simpl.
destruct n; rewrite H0; auto.
specialize (H1 n (le_n _)).
destruct (h n) eqn:?H; [| congruence].
destruct n; rewrite H; auto.
+
simpl.
rewrite (stream_sound1 h n (S (d + n))) by (auto; omega).
Admitted.

Lemma stream_app_spec1 {A: Type}: forall (h1 h2: stream A) (m: nat), is_at_least_n_stream (S m) h1 -> stream_app h1 h2 m = h1 m.
Proof.
intros.
simpl.
rewrite partial_stream_len_None by auto.
Admitted.

Lemma stream_app_spec1' {A: Type}: forall (h1 h2: stream A) (m: nat) a, h1 m = Some a -> stream_app h1 h2 m = Some a.
Proof.
intros.
rewrite stream_app_spec1; auto.
hnf; intros.
intro.
rewrite (stream_sound1 h1 n' m) in H by (auto; omega).
Admitted.

Lemma stream_app_spec2 {A: Type}: forall (h1 h2: stream A) (n m: nat), is_n_stream n h1 -> stream_app h1 h2 (m + n) = h2 m.
Proof.
intros.
simpl.
erewrite partial_stream_len_Some; [| | eassumption]; [| omega].
Admitted.

Lemma stream_app_empty_stream {A: Type}: forall (h: stream A), stream_app h empty_stream = h.
Proof.
intros.
stream_extensionality n.
destruct (at_most_n_stream_or_at_least_Sn_stream h n).
+
rewrite at_most_n_stream_spec in H.
destruct H as [m [? ?]].
replace n with ((n - m) + m) at 1 by omega.
rewrite (stream_app_spec2 _ _ m) by auto.
destruct H0.
rewrite (stream_sound1 h m n) by (auto; omega).
rewrite empty_stream_spec; auto.
+
Admitted.

Lemma stream_app_fstn_skipn {A: Type}: forall (h: stream A) (n: nat), stream_app (fstn_stream n h) (skipn_stream n h) = h.
Proof.
intros.
destruct (at_most_n_stream_or_at_least_n_stream h n).
+
rewrite fstn_stream_eq by auto.
rewrite skipn_stream_empty by auto.
apply stream_app_empty_stream.
+
stream_extensionality m.
destruct (lt_dec m n).
-
rewrite stream_app_spec1.
*
rewrite fstn_stream_Some by auto.
auto.
*
apply fstn_stream_is_n_stream in H.
rewrite at_least_n_stream_spec; left; exists n.
split; [omega | auto].
-
replace m with ((m - n) + n) at 1 by omega.
rewrite (stream_app_spec2 _ _ n).
*
rewrite skipn_stream_spec.
f_equal; omega.
*
Admitted.

Lemma stream_map_stream_app {A B: Type}: forall (f: A -> B) (h1 h2: stream A), stream_map f (stream_app h1 h2) = stream_app (stream_map f h1) (stream_map f h2).
Proof.
intros.
stream_extensionality n.
destruct (at_most_n_stream_or_at_least_Sn_stream h1 n).
+
rewrite at_most_n_stream_spec in H.
destruct H as [m [? ?]].
replace n with ((n - m) + m) by omega.
rewrite stream_map_spec.
rewrite stream_app_spec2 by auto.
rewrite stream_app_spec2 by (apply stream_map_n_stream; auto).
rewrite stream_map_spec.
reflexivity.
+
rewrite stream_app_spec1 by (apply stream_map_at_least_n_stream; auto).
rewrite stream_map_spec.
rewrite stream_app_spec1 by auto.
rewrite stream_map_spec.
Admitted.

Lemma stream_app_fstn_stream {A: Type}: forall (h1 h2: stream A) (n: nat), is_n_stream n h1 -> fstn_stream n (stream_app h1 h2) = h1.
Proof.
intros.
stream_extensionality m.
destruct (lt_dec m n).
+
rewrite fstn_stream_Some by auto.
rewrite stream_app_spec1; auto.
rewrite at_least_n_stream_spec; left; exists n.
split; [omega | auto].
+
rewrite fstn_stream_None by omega.
destruct H as [? _].
rewrite (stream_sound1 h1 n m) by (auto; omega).
Admitted.

Lemma stream_app_skipn_stream {A: Type}: forall (h1 h2: stream A) (n: nat), is_n_stream n h1 -> skipn_stream n (stream_app h1 h2) = h2.
Proof.
intros.
stream_extensionality m.
rewrite skipn_stream_spec.
Admitted.

Lemma partial_stream_clen'_None_iff {A: Type}: forall (h: nat -> stream A) (n: nat), match partial_stream_clen' h n return option A with | Some (k, m) => h k m | None => None end = None <-> partial_stream_clen' h n = None.
Proof.
intros.
induction n.
+
destruct (partial_stream_clen' h 0) as [[? ?] |] eqn:?H; [| tauto].
simpl in H.
destruct ((h 0) 0) eqn:?H; [| congruence].
inversion H; subst.
rewrite H0.
split; intro; congruence.
+
Opaque partial_stream_clen.
simpl.
Transparent partial_stream_clen.
destruct (partial_stream_clen h (S n)); auto.
destruct ((h n0) n1) eqn:?H, (partial_stream_clen' h n); auto; try tauto.
rewrite H.
Admitted.

Lemma partial_stream_clen_inf0 {A: Type}: forall (h: nat -> stream A) (n: nat), is_inf_stream (h 0) -> partial_stream_clen h n = (0, n).
Proof.
intros.
induction n.
+
simpl.
destruct ((h 0) 0) eqn:?H; auto.
+
simpl.
rewrite IHn.
destruct ((h 0) (S n)) eqn:?H; auto.
Admitted.

Lemma partial_stream_len_None {A: Type}: forall (h: stream A) (m: nat), is_at_least_n_stream (S m) h -> partial_stream_len h m = None.
Proof.
intros.
unfold partial_stream_len.
specialize (H m (le_n _)).
destruct (h m); auto; congruence.

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

Definition fin_stream {A: Type} (h: list A) : stream A.
exists (fun n => nth_error h n).
intros.
rewrite nth_error_None_iff in H0 |- *.
Admitted.

Definition inf_stream {A: Type} (h: nat -> A) : stream A.
exists (fun n => Some (h n)).
intros.
Admitted.

Lemma inf_stream_inf {A: Type}: forall f: nat -> A, is_inf_stream (inf_stream f).
Proof.
intros; hnf; intros.
simpl.
Admitted.

Lemma fin_stream_n_stream {A: Type}: forall l: list A, is_n_stream (length l) (fin_stream l).
Proof.
intros.
split.
+
simpl.
apply nth_error_None_iff; omega.
+
intros.
simpl.
Admitted.

Definition empty_stream_spec {A: Type}: forall n, @empty_stream A n = None.
Proof.
intros.
simpl.
Admitted.

Lemma empty_stream_is_empty {A: Type}: is_empty_stream (@empty_stream A).
Proof.
split.
+
apply empty_stream_spec.
+
Admitted.

Lemma stream_map_spec {A B: Type}: forall (f: A -> B) (h: stream A) (n: nat), stream_map f h n = match h n return option B with | Some a => Some (f a) | None => None end.
Proof.
Admitted.

Lemma stream_map_empty_stream {A B: Type}: forall (f: A -> B), stream_map f empty_stream = empty_stream.
Proof.
intros.
stream_extensionality n.
rewrite stream_map_spec, !empty_stream_spec.
Admitted.

Lemma stream_map_n_stream {A B: Type}: forall (f: A -> B) (h: stream A) (n: nat), is_n_stream n h <-> is_n_stream n (stream_map f h).
Proof.
intros.
split; intro.
+
destruct H; split.
-
rewrite stream_map_spec, H; auto.
-
intros; specialize (H0 n' H1).
destruct (h n') eqn:HH; rewrite stream_map_spec, HH; congruence.
+
destruct H; split.
-
destruct (h n) eqn:HH; rewrite stream_map_spec, HH in H; congruence.
-
intros; specialize (H0 n' H1).
Admitted.

Lemma stream_map_inf_stream {A B: Type}: forall (f: A -> B) (h: stream A), is_inf_stream h <-> is_inf_stream (stream_map f h).
Proof.
intros.
split; intro.
+
hnf; intros.
specialize (H n).
destruct (h n) eqn:HH; rewrite stream_map_spec, HH; congruence.
+
hnf; intros; specialize (H n).
Admitted.

Lemma stream_map_fin_stream {A B: Type}: forall (f: A -> B) (h: stream A), is_fin_stream h <-> is_fin_stream (stream_map f h).
Proof.
intros.
rewrite !is_fin_stream_spec.
apply Morphisms_Prop.ex_iff_morphism; intros ?.
Admitted.

Lemma stream_map_at_least_n_stream {A B: Type}: forall (f: A -> B) (h: stream A) (n: nat), is_at_least_n_stream n h <-> is_at_least_n_stream n (stream_map f h).
Proof.
intros.
rewrite !at_least_n_stream_spec.
apply Morphisms_Prop.or_iff_morphism.
+
apply Morphisms_Prop.ex_iff_morphism; intro.
apply Morphisms_Prop.and_iff_morphism; [reflexivity |].
apply stream_map_n_stream; auto.
+
Admitted.

Lemma stream_map_at_most_n_stream {A B: Type}: forall (f: A -> B) (h: stream A) (n: nat), is_at_most_n_stream n h <-> is_at_most_n_stream n (stream_map f h).
Proof.
intros.
rewrite !at_most_n_stream_spec.
apply Morphisms_Prop.ex_iff_morphism; intro.
apply Morphisms_Prop.and_iff_morphism; [reflexivity |].
Admitted.

Definition skipn_stream {A: Type} (n: nat) (h: stream A) : stream A.
exists (fun m => h (m + n)).
intros.
revert H0; apply (stream_sound1 h).
Admitted.

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

Lemma fin_stream_fin {A: Type}: forall l: list A, is_fin_stream (fin_stream l).
Proof.
intros.
exists (length l).
simpl.
rewrite nth_error_None_iff; auto.

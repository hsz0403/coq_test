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

Lemma stream_capp_spec2 {A: Type}: forall (h: nat -> stream A) (n m: nat), n > 0 -> is_n_stream n (h 0) -> stream_capp h (m + n) = stream_capp (fun n => h (S n)) m.
Proof.
intros.
simpl.
rewrite (partial_stream_clen'_fin0_right _ _ m H H0).
destruct (partial_stream_clen' (fun n0 : nat => h (S n0)) m) as [[? ?] |]; auto.

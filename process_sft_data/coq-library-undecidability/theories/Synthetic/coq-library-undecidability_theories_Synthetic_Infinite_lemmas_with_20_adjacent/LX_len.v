From Undecidability Require Import Shared.ListAutomation Shared.Dec.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts MoreEnumerabilityFacts.
Require Import Arith ConstructiveEpsilon.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Definition mu (p : nat -> Prop) : (forall x, dec (p x)) -> ex p -> sig p.
Proof.
apply constructive_indefinite_ground_description_nat.
Defined.
Notation mu' d H := (proj1_sig (mu d H)).
Definition generating X := forall (A : list X), exists x, ~ x el A.
Definition injective X Y (f : X -> Y) := forall x x', f x = f x' -> x = x'.
Definition infinite X := exists (f : nat -> X), injective f.
Section Inf.
Variables (X : Type) (f' : nat -> option X).
Hypothesis Hf' : forall x, exists n, f' n = Some x.
Hypothesis HX : eq_dec X.
Section Gen.
Variable f : nat -> X.
Hypothesis Hf : injective f.
Fixpoint LX n := match n with | 0 => [f 0] | S n => f (S n) :: LX n end.
End Gen.
Hypothesis Hg : generating X.
Instance el_dec : forall (A : list X) x, dec (x el A).
Proof.
intros A x.
induction A; cbn; auto.
Definition dummy : X.
Proof.
pose (p := fun n => exists x, f' n = Some x).
destruct (@mu p) as [n Hn].
-
intros n.
destruct (f' n) eqn : H.
+
left.
now exists x.
+
right.
intros [x H'].
congruence.
-
destruct (Hg nil) as [x Hx].
destruct (Hf' x) as [n Hn].
now exists n, x.
-
destruct (f' n) eqn : H; trivial.
exfalso.
destruct Hn as [x Hx].
congruence.
Definition f n := match (f' n) with Some x => x | None => dummy end.
Definition le_f x y := exists n, f n = x /\ forall n', f n' = y -> n <= n'.
Fixpoint LL n := match n with 0 => nil | S n => LL n ++ [gen' (LL n)] end.
Definition F n := gen' (LL n).
Definition G x := mu' _ (F_sur x).
End Inf.

Definition mu (p : nat -> Prop) : (forall x, dec (p x)) -> ex p -> sig p.
Proof.
Admitted.

Lemma mu_least (p : nat -> Prop) (d : forall x, dec (p x)) (H : ex p) : forall n, p n -> mu' d H <= n.
Proof.
intros n H'.
destruct (Nat.le_gt_cases (mu' d H) n) as [Hl | Hl]; eauto.
exfalso.
eapply linear_search_smallest with (start := 0).
2: exact H'.
split.
lia.
Admitted.

Lemma LX_el n x : x el LX n -> exists n', n' <= n /\ f n' = x.
Proof.
induction n.
-
intros [H|[] ].
exists 0.
split; auto.
-
intros [H|H]; eauto.
destruct (IHn H) as [n'[H1 H2] ].
exists n'.
Admitted.

Lemma LX_NoDup n : NoDup (LX n).
Proof.
induction n; cbn; repeat constructor; auto.
intros (n'&H1&H2) % LX_el.
apply Hf in H2.
Admitted.

Lemma sub_dec (A B : list X) : (A <<= B) + {x | x el A /\ ~ x el B}.
Proof.
revert B.
induction A; intros B; cbn; auto.
destruct (IHA B); decide (a el B); auto.
-
right.
exists a.
split; auto.
-
destruct s as (x&H1&H2).
right.
exists x.
split; auto.
-
right.
exists a.
Admitted.

Lemma X_gen : generating X.
Proof.
intros A.
destruct (sub_dec (LX (length A)) A) as [H|H].
-
apply NoDup_incl_length in H; try apply LX_NoDup.
rewrite LX_len in H.
lia.
-
destruct H as [x [_ H] ].
Admitted.

Instance el_dec : forall (A : list X) x, dec (x el A).
Proof.
intros A x.
Admitted.

Definition dummy : X.
Proof.
pose (p := fun n => exists x, f' n = Some x).
destruct (@mu p) as [n Hn].
-
intros n.
destruct (f' n) eqn : H.
+
left.
now exists x.
+
right.
intros [x H'].
congruence.
-
destruct (Hg nil) as [x Hx].
destruct (Hf' x) as [n Hn].
now exists n, x.
-
destruct (f' n) eqn : H; trivial.
exfalso.
destruct Hn as [x Hx].
Admitted.

Lemma f_sur : forall x, exists n, f n = x.
Proof.
intros x.
destruct (Hf' x) as [n Hn].
exists n.
unfold f.
Admitted.

Lemma gen (A : list X) : { x | ~ x el A /\ forall y, ~ y el A -> le_f x y}.
Proof.
pose (p := fun n => ~ f n el A).
assert (H1 : forall x, dec (p x)).
{
intros n.
destruct (el_dec A (f n)) as [H|H].
-
right.
intros H'.
contradiction.
-
left.
assumption.
}
assert (H2 : exists x, p x).
{
destruct (Hg A) as [x Hx].
destruct (f_sur x) as [n <-].
now exists n.
}
exists (f (mu' H1 H2)).
split; try apply proj2_sig.
intros y Hy.
exists (mu' H1 H2).
split; trivial.
intros n <-.
Admitted.

Lemma gen_spec A : ~ gen' A el A.
Proof.
unfold gen'.
destruct (gen A); cbn.
Admitted.

Lemma gen_le_f A : forall x, ~ x el A -> le_f (gen' A) x.
Proof.
unfold gen'.
destruct (gen A); cbn.
Admitted.

Lemma LL_cum : cumulative LL.
Proof.
intros n.
Admitted.

Lemma F_nel n : ~ F n el LL n.
Proof.
Admitted.

Lemma F_el n : F n el LL (S n).
Proof.
cbn.
apply in_app_iff.
Admitted.

Lemma F_lt n m : n < m -> F n el LL m.
Proof.
intros H.
apply (cum_ge' (n:=S n)).
-
apply LL_cum.
-
apply F_el.
-
Admitted.

Lemma F_inj' n m : F n = F m -> ~ n < m.
Proof.
intros H1 H2 % F_lt.
rewrite H1 in H2.
Admitted.

Lemma F_inj : injective F.
Proof.
intros n m Hnm.
destruct (Nat.lt_total n m) as [H|[H|H] ]; trivial.
-
contradiction (F_inj' Hnm H).
-
symmetry in Hnm.
Admitted.

Lemma lt_acc n : Acc lt n.
Proof.
induction n.
-
constructor.
intros m H.
lia.
-
constructor.
intros m H.
destruct (Nat.lt_total n m) as [H'|[->|H'] ].
+
lia.
+
assumption.
+
Admitted.

Lemma LL_f n : f n el LL (S n).
Proof.
induction (lt_acc n) as [n _ IH].
decide _; try eassumption.
exfalso.
assert (H : ~ f n el LL n).
{
intros H.
apply n0.
apply (cum_ge' LL_cum H).
auto.
}
apply gen_le_f in H as [n'[H1 H2] ].
specialize (H2 n eq_refl).
destruct (Nat.lt_total n' n) as [H3|[->|H3] ].
-
apply (gen_spec (A:=LL n)).
rewrite <- H1.
now apply (cum_ge' LL_cum (IH n' H3)).
-
apply n0.
rewrite H1.
apply in_app_iff; fold LL.
right.
left.
reflexivity.
-
Admitted.

Lemma LL_F x n : x el LL n -> exists m, F m = x.
Proof.
induction n; cbn; auto.
intros [H|[H|H]] % in_app_iff; auto.
Admitted.

Lemma F_sur : forall x, exists n, F n = x.
Proof.
intros x.
destruct (f_sur x) as [n H].
destruct (LL_F (LL_f n)) as [m H'].
exists m.
Admitted.

Lemma LX_len n : length (LX n) = S n.
Proof.
induction n; cbn; eauto.

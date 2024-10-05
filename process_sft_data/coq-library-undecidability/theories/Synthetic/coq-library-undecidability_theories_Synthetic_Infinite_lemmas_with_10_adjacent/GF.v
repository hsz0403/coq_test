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

Lemma FG n : F (G n) = n.
Proof.
unfold G.
Admitted.

Lemma GF n : G (F n) = n.
Proof.
apply F_inj.
now rewrite FG.

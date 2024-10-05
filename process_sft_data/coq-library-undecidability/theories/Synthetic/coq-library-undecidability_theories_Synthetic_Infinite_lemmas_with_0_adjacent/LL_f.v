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

Lemma LL_F x n : x el LL n -> exists m, F m = x.
Proof.
induction n; cbn; auto.
intros [H|[H|H]] % in_app_iff; auto.
now exists n.

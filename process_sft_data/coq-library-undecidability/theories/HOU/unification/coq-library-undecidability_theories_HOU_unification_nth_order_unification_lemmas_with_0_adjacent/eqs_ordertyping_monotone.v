Require Import List Lia Morphisms.
From Undecidability.HOU Require Import std.std calculus.calculus unification.higher_order_unification unification.systemunification.
Import ListNotations.
Set Default Proof Using "Type".
Section NthOrderUnificationDefinition.
Context {n: nat} {X: Const}.
Class orduni := { Gamma₀ : ctx; s₀ : exp X; t₀ : exp X; A₀ : type; H1₀ : Gamma₀ ⊢(n) s₀ : A₀; H2₀ : Gamma₀ ⊢(n) t₀ : A₀ }.
Definition OU (I: orduni) := exists (Delta: ctx) (sigma: fin -> exp X), Delta ⊩(n) sigma : Gamma₀ /\ sigma • s₀ ≡ sigma • t₀.
End NthOrderUnificationDefinition.
Arguments orduni _ : clear implicits.
Arguments OU _ : clear implicits.
Hint Resolve H1₀ H2₀ : core.
Section NthOrderSystemUnification.
Variable (X: Const).
Implicit Types (sigma: fin -> exp X) (e: eq X) (E : eqs X).
Definition eq_ordertyping n Gamma e A := Gamma ⊢(n) fst e : A /\ Gamma ⊢(n) snd e : A.
Notation "Gamma ⊢₂( n ')' e : A" := (eq_ordertyping n Gamma e A) (at level 80, e at level 99).
Reserved Notation "Gamma ⊢₊₊( n ) E : L" (at level 80, E at level 99).
Inductive eqs_ordertyping Gamma n : eqs X -> list type -> Prop := | eqs_ordertyping_nil: Gamma ⊢₊₊(n) nil : nil | eqs_ordertyping_cons s t A E L: Gamma ⊢(n) s : A -> Gamma ⊢(n) t : A -> Gamma ⊢₊₊(n) E : L -> Gamma ⊢₊₊(n) ((s,t) :: E) : A :: L where "Gamma ⊢₊₊( n ) E : L" := (eqs_ordertyping Gamma n E L).
Hint Constructors eqs_ordertyping : core.
Hint Resolve left_typing right_typing left_ordertyping right_ordertyping : core.
Hint Rewrite Vars'_cons Vars'_app : simplify.
Hint Rewrite left_subst_eqs right_subst_eqs : simplify.
Class ordsysuni (n: nat) := { Gamma₀' : ctx; E₀' : eqs X; L₀' : list type; H₀' : Gamma₀' ⊢₊₊(n) E₀' : L₀'; }.
Definition SOU n (I: ordsysuni n) := exists (Delta: ctx) (sigma: fin -> exp X), Delta ⊩(n) sigma : Gamma₀' /\ forall s t, (s, t) ∈ E₀' -> sigma • s ≡ sigma • t.
Arguments SOU: clear implicits.
Hint Resolve H₀' : core.
Hint Resolve linearize_terms_ordertyping : core.
Global Instance orduni_ordsysuni n (I: orduni n X): ordsysuni n.
Proof.
refine {| Gamma₀' := Gamma₀; E₀' := [(s₀, t₀)]; L₀' := [A₀]; H₀' := _; |}.
abstract (eauto).
Defined.
Global Instance ordsysuni_orduni {n} (I: ordsysuni n): ord' L₀' < n -> orduni n X.
Proof.
intro H.
refine {| Gamma₀ := Gamma₀'; s₀ := linearize_terms (left_side E₀'); t₀ := linearize_terms (right_side E₀'); A₀ := (Arr (rev L₀') alpha) → alpha; H1₀ := _; H2₀ := _; |}.
-
abstract (assert (1 <= n) by (destruct n; lia); eauto).
-
abstract (assert (1 <= n) by (destruct n; lia); eauto).
Defined.
End NthOrderSystemUnification.
Arguments SOU : clear implicits.
Arguments ordsysuni : clear implicits.
Arguments Gamma₀' {_} {_} {_}.
Arguments E₀' {_} {_} {_}.
Arguments L₀' {_} {_} {_}.
Notation "Gamma ⊢₊₊( n ) E : L" := (eqs_ordertyping _ Gamma n E L)(at level 80, E at level 99).
Notation "Gamma ⊢₂( n ')' e : A" := (eq_ordertyping _ n Gamma e A) (at level 80, e at level 99).
Hint Resolve eqs_ordertyping_soundness : core.
Definition NOU {X: Const} n (I: orduni n X) := exists Delta sigma, Delta ⊩(n) sigma : Gamma₀ /\ sigma • s₀ ≡ sigma • t₀ /\ forall x, normal (sigma x).
Definition NSOU {X: Const} n (I: ordsysuni X n) := exists Delta sigma, Delta ⊩(n) sigma : Gamma₀' /\ (forall s t, (s, t) ∈ E₀' -> sigma • s ≡ sigma • t) /\ forall x, normal (sigma x).
Section SubstitutionTransformations.
Variable (X: Const) (n: nat) (s t: exp X) (A: type) (Gamma: ctx).
Hypothesis (Leq: 1 <= n).
Hypothesis (T1: Gamma ⊢(n) s : A) (T2: Gamma ⊢(n) t : A).
Implicit Types (Delta: ctx) (sigma : fin -> exp X).
End SubstitutionTransformations.
Section Normalisation.
Variable (X: Const).
Arguments s₀ {_} {_} _.
Arguments t₀ {_} {_} _.
Arguments Gamma₀ {_} {_} _.
Arguments A₀ {_} {_} _.
Arguments sᵤ {_} _.
Arguments tᵤ {_} _.
Arguments Gammaᵤ {_} _.
Arguments Aᵤ {_} _.
Program Instance orduni_normalise n (I: orduni n X) : orduni n X := { Gamma₀ := Gamma₀ I; s₀ := eta₀ (s₀ I) H1₀; t₀ := eta₀ (t₀ I) H2₀; A₀ := A₀ I }.
Next Obligation.
eapply ordertyping_preservation_under_steps.
rewrite <-eta₀_correct.
all: eauto.
Next Obligation.
eapply ordertyping_preservation_under_steps.
rewrite <-eta₀_correct.
all: eauto.
End Normalisation.

Lemma eqs_ordertyping_monotone Gamma n m E L: n <= m -> Gamma ⊢₊₊(n) E : L -> Gamma ⊢₊₊(m) E : L.
Proof.
induction 1; eauto using eqs_ordertyping_step.

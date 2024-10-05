Set Implicit Arguments.
Require Import List Lia.
From Undecidability.HOU Require Import std.std calculus.calculus unification.higher_order_unification.
Import ListNotations.
Set Default Proof Using "Type".
Section SystemUnification.
Variable (X: Const).
Definition eq: Type := exp X * exp X.
Definition eqs := list eq.
Implicit Types (sigma: fin -> exp X) (e: eq) (E : eqs).
Definition eq_typing Gamma e A := Gamma ⊢ fst e : A /\ Gamma ⊢ snd e : A.
Notation "Gamma ⊢₂ e : A" := (eq_typing Gamma e A) (at level 80, e at level 99).
Reserved Notation "Gamma ⊢₊₊ E : L" (at level 80, E at level 99).
Inductive eqs_typing Gamma : eqs -> list type -> Prop := | eqs_typing_nil: Gamma ⊢₊₊ nil : nil | eqs_typing_cons s t A E L: Gamma ⊢ s : A -> Gamma ⊢ t : A -> Gamma ⊢₊₊ E : L -> Gamma ⊢₊₊ ((s,t) :: E) : A :: L where "Gamma ⊢₊₊ E : L" := (eqs_typing Gamma E L).
Hint Constructors eqs_typing : core.
Definition left_side E := map fst E.
Definition right_side E := map snd E.
Hint Resolve left_typing right_typing : core.
Definition vars' (e: eq) := vars (fst e) ++ vars (snd e).
Definition Vars' (E: list eq) := flat_map vars' E.
Hint Rewrite Vars'_cons Vars'_app : simplify.
Definition subst_eq sigma e := let (s, t) := e in (sigma • s, sigma • t).
Notation "sigma •₊₊ E" := (map (subst_eq sigma) E) (at level 69, right associativity).
Hint Rewrite left_subst_eqs right_subst_eqs : simplify.
Definition all_terms (P: exp X -> Prop) (E: eqs) := forall s t, (s, t) ∈ E -> P s /\ P t.
Definition all_eqs (P: exp X -> exp X -> Prop) (E: eqs) := forall s t, (s, t) ∈ E -> P s t.
Hint Rewrite all_terms_cons_iff : simplify.
Hint Rewrite all_terms_app : simplify.
Class sysuni := { Gammaᵤ' : ctx; Eᵤ' : eqs; Lᵤ' : list type; Hᵤ' : Gammaᵤ' ⊢₊₊ Eᵤ' : Lᵤ'; }.
Definition SU (I: sysuni) := exists (Delta: ctx) (sigma: fin -> exp X), (Delta ⊩ sigma : Gammaᵤ') /\ forall s t, (s, t) ∈ Eᵤ' -> sigma • s ≡ sigma • t.
Arguments SU: clear implicits.
Hint Resolve Hᵤ' : core.
Definition linearize_terms (S: list (exp X)) := lambda AppR (var 0) (renL shift S).
Hint Resolve linearize_terms_typing : core.
Section Interreducible.
Global Program Instance uni_sysuni (I: uni X): sysuni := { Gammaᵤ' := Gammaᵤ; Eᵤ' := [(sᵤ, tᵤ)]; Lᵤ' := [Aᵤ]; Hᵤ' := _; }.
Global Program Instance sysuni_uni (I: sysuni): uni X := { Gammaᵤ := Gammaᵤ'; sᵤ := linearize_terms (left_side Eᵤ'); tᵤ := linearize_terms (right_side Eᵤ'); Aᵤ := (Arr (rev Lᵤ') alpha) → alpha; H1ᵤ := _; H2ᵤ := _; }.
End Interreducible.
End SystemUnification.
Arguments SU : clear implicits.
Arguments sysuni : clear implicits.
Arguments Gammaᵤ' {_} {_}.
Arguments Eᵤ' {_} {_}.
Arguments Lᵤ' {_} {_}.
Notation "sigma •₊₊ E" := (map (subst_eq sigma) E) (at level 69, right associativity).
Notation "Gamma ⊢₊₊ E : L" := (eqs_typing Gamma E L) (at level 80, E at level 99).
Notation "Gamma ⊢₂ e : A" := (eq_typing Gamma e A) (at level 80, e at level 99).
Hint Rewrite all_terms_cons_iff all_terms_app Vars'_app Vars'_cons: simplify.
Hint Resolve all_terms_nil : core.
Definition NSU {X: Const} (I: sysuni X) := exists Delta sigma, Delta ⊩ sigma : Gammaᵤ' /\ (forall s t, (s, t) ∈ Eᵤ' -> sigma • s ≡ sigma • t) /\ forall x, normal (sigma x).

Lemma left_typing Gamma E L: Gamma ⊢₊₊ E : L -> Gamma ⊢₊ left_side E : L.
Proof.
induction 1; cbn; eauto.

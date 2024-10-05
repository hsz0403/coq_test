Set Implicit Arguments.
Require Import RelationClasses Morphisms List Lia Init.Nat Setoid.
From Undecidability.HOU Require Import std.std calculus.calculus unification.unification.
From Undecidability.HOU Require Import third_order.pcp third_order.encoding.
Import ListNotations.
Set Default Proof Using "Type".
Definition MPCP' '(c, C) := exists I, I ⊆ nats (length C) /\ hd c ++ @concat symbol (select I (heads C)) = tl c ++ concat (select I (tails C)).
Section SimplifiedReduction.
Variable (X: Const).
Definition redtm (w: word) (W: list word): exp X := lambda lambda (enc 0 1 w) (AppR (var 2) (Enc 0 1 W)).
Definition redctx (n: nat) := [Arr (repeat (alpha → alpha) n) alpha].
Program Instance MPCP'_to_U P : orduni 3 X := { Gamma₀ := redctx (length (snd P)); s₀ := redtm (hd (fst P)) (heads (snd P)); t₀ := redtm (tl (fst P)) (tails (snd P)); A₀ := (alpha → alpha) → (alpha → alpha) → alpha; H1₀ := redtm_typing (hd (fst P)) (heads (snd P)); H2₀ := redtm_typing (tl (fst P)) (tails (snd P)); }.
Next Obligation.
now simplify.
Next Obligation.
now simplify.
End SimplifiedReduction.

Lemma MPCP_U3 X: MPCP ⪯ OU 3 X.
Proof.
exists (fun '(c, C) => MPCP'_to_U X (c, c::C)).
intros [c C]; rewrite MPCP_MPCP'; split.
all: eauto using MPCP'_U3, U3_MPCP'.

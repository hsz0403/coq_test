Set Implicit Arguments.
Require Import Lia List.
From Undecidability.HOU Require Import calculus.calculus concon.conservativity_constants unification.higher_order_unification unification.systemunification unification.nth_order_unification.
Import ListNotations.
Set Default Proof Using "Type".
Hint Rewrite @consts_Lam @consts_AppL @consts_AppR : simplify.
Section InhabitingTypes.
Variable (X: Const).
Implicit Types (s t: exp X) (Gamma Delta: ctx) (sigma tau: fin -> exp X).
Definition inhab (x: fin) (A: type) := Lambda (arity A) (@var X (arity A + x)).
End InhabitingTypes.
Hint Resolve inhab_app inhab_typing inhab_typing' ord_target' : core.
Section Conservativity.
Variable (X: Const).
Section DowncastLemmas.
Implicit Types (s t: exp X) (Gamma: ctx) (A: type).
Variable (n: nat).
Hypothesis (Leq: 1 <= n).
End DowncastLemmas.
Program Instance unification_monotone {n} (D: orduni n X): orduni (S n) X := { Gamma₀ := Gamma₀; s₀ := s₀ ; t₀ := t₀; A₀ := A₀; }.
Program Instance unification_conservative {n} (D: orduni n X): uni X := { Gammaᵤ := Gamma₀; sᵤ := s₀ ; tᵤ := t₀; Aᵤ := A₀; }.
Next Obligation.
eapply ordertyping_soundness; eauto.
Next Obligation.
eapply ordertyping_soundness; eauto.
Program Instance SU_monotone {n} (I: ordsysuni X n): ordsysuni X (S n) := { Gamma₀' := @Gamma₀' _ _ I; E₀' := @E₀' _ _ I ; L₀' := @L₀' _ _ I; }.
Next Obligation.
eapply eqs_ordertyping_step, @H₀'.
Program Instance SU_conservative {n} (I: ordsysuni X n): sysuni X := { Gammaᵤ' := @Gamma₀' _ _ I; Eᵤ' := @E₀' _ _ I ; Lᵤ' := @L₀' _ _ I; }.
Next Obligation.
eapply eqs_ordertyping_soundness, H₀'.
End Conservativity.

Lemma downcast_constants_ordered m Gamma s t Delta sigma: 1 <= m -> Delta ⊩(m) sigma : Gamma -> sigma • s ≡ sigma • t -> exists Sigma tau, Delta ++ Sigma ⊩(m) tau : Gamma /\ tau • s ≡ tau • t /\ ord' Sigma <= 1 /\ (forall x c, c ∈ consts (tau x) -> c ∈ Consts [s; t]).
Proof.
intros L' T EQ.
pose (C0 := Consts [s; t]).
pose (C := Consts (map sigma (nats (length Gamma)))).
pose (zeta c := match find c C0 with | Some n => const c | None => match find c C with | Some x => inhab X (length Delta + x) (ctype X c) | None => var 0 end end).
exists (target' (map (ctype X) C)).
exists (sigma >> subst_consts zeta).
intuition.
-
intros ???.
eapply ordertyping_preservation_consts.
now eapply weakening_ordertyping_app, T.
intros c H1.
unfold zeta.
destruct (find c C0); eauto.
+
econstructor; eapply typing_constants; eauto.
+
eapply Consts_consts with (S := (map sigma (nats (length Gamma)))) in H1 as H2.
unfold C; eapply find_in in H2 as [y H2].
rewrite H2.
eapply ordertyping_monotone, inhab_app, inhab_typing'; eauto.
erewrite map_nth_error; eauto.
now eapply find_Some.
eapply in_map, lt_nats, nth_error_Some_lt; eauto.
-
rewrite !subst_const_comm_id.
now rewrite EQ.
all: eapply subst_consts_ident; intros x; rewrite Consts_consts with (S := [s; t]); intuition.
all: now unfold zeta, C0; eapply find_in in H as [? ->].
-
eapply consts_in_subst_consts in H as [d []].
unfold zeta in *.
destruct find eqn: H1.
+
cbn in H0; intuition; subst.
eapply find_Some, nth_error_In in H1; exact H1.
+
destruct (find d C) eqn: H2.
all: rewrite ?consts_inhab in H0; cbn in H0; intuition.

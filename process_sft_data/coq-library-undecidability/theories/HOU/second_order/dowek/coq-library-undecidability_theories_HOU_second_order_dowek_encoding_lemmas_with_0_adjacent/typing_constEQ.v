Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.
From Undecidability.HOU Require Import std.std calculus.calculus second_order.diophantine_equations.
From Undecidability.HOU.unification Require Import systemunification nth_order_unification.
Set Default Proof Using "Type".
Section ChurchEncoding.
Context {X: Const}.
Implicit Type (n c: nat) (x y z: fin) (e: deq) (E: list deq).
Definition enc n : exp X := lambda lambda AppL (repeat (var 0) n) (var 1).
Definition add (s t: exp X) := lambda lambda (ren (shift >> shift) s) ((ren (shift >> shift) t) (var 1) (var 0)) (var 0).
Definition mul (s t: exp X) := lambda lambda (ren (shift >> shift) s) (var 1) (lambda ((ren (shift >> shift >> shift) t) (var 0) (var 1))).
Section Substitution.
End Substitution.
Hint Rewrite add_ren add_subst mul_ren mul_subst enc_ren enc_subst : asimpl.
Hint Rewrite enc_zero enc_succ : simplify.
Hint Resolve normal_enc : core.
End ChurchEncoding.
Hint Rewrite @add_ren @add_subst @mul_ren @mul_subst @enc_ren @enc_subst : asimpl.
Section Encoding.
Context {X: Const}.
Implicit Type (n c: nat) (x y z: fin) (e: deq) (E: list deq).
Definition varEQ x: eq X := (lambda lambda (var 0) (var (S (S x)) (var 1) (var 0)), lambda lambda (var (S (S x))) ((var 0) (var 1)) (var 0)).
Definition constEQ (x: nat): eq X := (var x, enc 1).
Definition addEQ (x y z: nat): eq X := (add (var x) (var y), var z).
Definition mulEQ (x y z: nat) : eq X := (mul (var x) (var y), var z).
Definition eqs (e: deq) : eqs X := match e with | x =ₑ 1 => [varEQ x; constEQ x] | x +ₑ y =ₑ z => [varEQ x; varEQ y; varEQ z; addEQ x y z] | x *ₑ y =ₑ z => [varEQ x; varEQ y; varEQ z; mulEQ x y z] end.
Notation Eqs E := (flat_map eqs E).
Section Typing.
Variable (E: list deq).
Hint Resolve Vars__de_in : core.
Definition Gamma__dwk := repeat (alpha → (alpha → alpha) → alpha) (S (Sum (Vars__de E))).
Hint Resolve Gamma__dwk_nth : core.
End Typing.
End Encoding.
Hint Rewrite @enc_ren @enc_subst : asimpl.
Notation Eqs E := (flat_map eqs E).
Program Instance H10_to_DWK X (E: list deq): ordsysuni X 3 := { Gamma₀' := Gamma__dwk E; E₀' := Eqs E; L₀' := repeat (alpha → (alpha → alpha) → alpha) (length (Eqs E)); H₀' := _; }.
Next Obligation.
eapply ordertyping_combine.
all: unfold left_side, right_side.
all: eapply repeated_ordertyping; simplify; [|eauto].
all: intros ? ?; mapinj; eapply in_Equations in H1 as [? []];eapply typing_equations; eauto.

Lemma typing_constEQ x c: x =ₑ 1 ∈ E -> Gamma__dwk ⊢₂(3) constEQ x : alpha → (alpha → alpha) → alpha.
Proof.
intros; unfold constEQ.
split; cbn [fst snd].
+
econstructor; eauto.
eapply Gamma__dwk_nth, Vars__de_in; eauto; cbn; intuition.
+
eapply typing_enc.

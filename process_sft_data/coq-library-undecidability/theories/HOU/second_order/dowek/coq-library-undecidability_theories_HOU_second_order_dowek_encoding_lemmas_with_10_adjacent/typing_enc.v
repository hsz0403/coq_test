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

Lemma enc_ren n delta: ren delta (enc n) = enc n.
Proof.
unfold enc.
cbn.
do 2 f_equal.
asimpl.
Admitted.

Lemma enc_subst n sigma: sigma • (enc n) = enc n.
Proof.
unfold enc.
cbn.
do 2 f_equal.
asimpl.
Admitted.

Lemma add_ren s t delta: ren delta (add s t) = add (ren delta s) (ren delta t).
Proof.
Admitted.

Lemma add_subst s t sigma: sigma • (add s t) = add (sigma • s) (sigma • t).
Proof.
unfold add; asimpl; cbn.
do 4 f_equal.
now asimpl.
Admitted.

Lemma mul_ren s t delta: ren delta (mul s t) = mul (ren delta s) (ren delta t).
Proof.
Admitted.

Lemma mul_subst s t sigma: sigma • (mul s t) = mul (sigma • s) (sigma • t).
Proof.
unfold mul; asimpl; cbn.
do 4 f_equal.
now asimpl.
Admitted.

Lemma enc_app n s t: enc n s t ≡ AppL (repeat t n) s.
Proof.
unfold enc.
do 2 (rewrite stepBeta; asimpl; cbn; eauto).
Admitted.

Lemma enc_zero s f: enc 0 s f ≡ s.
Proof.
Admitted.

Lemma enc_succ n s f: enc (S n) s f ≡ f (enc n s f).
Proof.
Admitted.

Lemma enc_eta n: enc n ≡ lambda lambda (enc n) (var 1) (var 0).
Proof.
Admitted.

Lemma enc_add' n m s f: enc (n + m) s f ≡ (enc n) (enc m s f) f.
Proof.
induction n; cbn; simplify; eauto.
Admitted.

Lemma enc_add n m: enc (n + m) ≡ add (enc n) (enc m).
Proof.
unfold add; rewrite enc_eta; asimpl.
Admitted.

Lemma enc_mul' n m s f: enc (n * m) s f ≡ (enc n) s (lambda (enc m (var 0) (ren shift f))).
Proof.
induction n; cbn.
-
now simplify.
-
rewrite enc_add', IHn.
simplify.
Admitted.

Lemma enc_mul n m: enc (n * m) ≡ mul (enc n) (enc m).
Proof.
unfold mul; rewrite enc_eta; asimpl.
Admitted.

Lemma enc_injective n m: enc n = enc m -> n = m.
Proof.
injection 1 as H.
induction n in m, H |-*; destruct m; try discriminate; eauto.
erewrite IHn; eauto.
Admitted.

Lemma normal_enc n: normal (enc n).
Proof.
do 2 eapply normal_lam_intro.
Admitted.

Lemma typing_enc Gamma n: Gamma ⊢(3) enc n : alpha → (alpha → alpha) → alpha.
Proof.
unfold enc.
econstructor.
econstructor.
eapply AppL_ordertyping_repeated; eauto.
eapply repeated_ordertyping; simplify; eauto.
intros ? <- % repeated_in; eauto.

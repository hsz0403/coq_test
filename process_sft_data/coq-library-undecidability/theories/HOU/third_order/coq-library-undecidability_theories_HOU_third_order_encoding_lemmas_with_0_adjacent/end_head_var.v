Set Implicit Arguments.
Require Import RelationClasses Morphisms List Lia Arith Lia Init.Nat Setoid.
From Undecidability.HOU Require Import std.std calculus.calculus third_order.pcp.
Import ListNotations.
Set Default Proof Using "Type".
Section Encoding.
Context {X: Const}.
Variable (u v: nat).
Hypothesis (u_neq_v: u <> v).
Definition encb (b: symbol) : exp X := var (if b then u else v).
Definition enc (w: word) : exp X := lambda (AppL (renL shift (map encb w)) (var 0)).
Notation Enc := (map enc).
Section Typing.
End Typing.
Section Reduction.
Hint Rewrite enc_nil enc_cons : simplify.
Hint Rewrite enc_app : simplify.
End Reduction.
Hint Rewrite enc_nil enc_cons enc_app : simplify.
Section Substitution.
End Substitution.
Definition nostring (t: exp X) := forall s, ~ t ≡ var u s /\ ~ t ≡ var v s.
Section Injectivity.
End Injectivity.
Section EquivalenceInversion.
Variables (s t: exp X) (x: nat) (sigma: fin -> exp X) (S: list (exp X)).
Hypothesis (H1: forall y, isVar (sigma y) /\ sigma y <> var x).
Hypothesis (N: normal s).
Hypothesis (EQ: S .+ sigma • s ≡ (var x) t).
End EquivalenceInversion.
Section MainLemma.
Variable (Gamma : ctx) (s: exp X) (n: nat).
Hypothesis (Ts: Gamma ⊢(3) s : Arr (repeat (alpha → alpha) n) alpha).
Hypothesis (Vu: ~ u ∈ vars s) (Vv: ~ v ∈ vars s).
End MainLemma.
End Encoding.
Hint Rewrite @enc_app @enc_nil: simplify.
Notation Enc u v := (map (enc u v)).
Section ReductionEncodings.
Context {X: Const}.
Definition finst I n := Lambda n (AppL (map var I) (@var X n)).
End ReductionEncodings.

Lemma end_head_var: exists (h: nat) T s', s = AppR (var h) T /\ nth S h = Some s'.
Proof using x v u_neq_v t sigma N H1 EQ.
eapply normal_nf in N as N'.
inv N'.
destruct k; cbn in *; (eauto 5); [|Discriminate].
destruct (s0); cbn in H; intuition idtac; clear H.
-
assert(f < |S| \/ f >= |S|) as [] by lia; (eauto 5).
eapply nth_error_lt_Some in H as H2; destruct H2; (eauto 5).
asimpl in EQ; rewrite sapp_ge_in in EQ; (eauto 2).
specialize (H1 (f - |S|)).
intuition.
eapply equiv_head_equal in EQ; cbn; simplify; (eauto 3).
simplify in EQ; cbn in EQ; (eauto 1).
destruct (sigma (f - (|S|))); cbn in *; intuition.
-
eauto.
asimpl in EQ.
eapply equiv_head_equal in EQ; cbn; simplify in *; (eauto 2).
cbn in EQ; discriminate.

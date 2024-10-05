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

Lemma AppL_decomposition (s: exp X) (n: nat): { '(I, u) | I ⊆ nats n /\ s = AppL (map var I) u /\ forall x v, u = var x v -> ~ x < n }.
Proof.
destruct (@AppL_largest _ (fun s => match s with var x => x < n | _ => False end) s) as (S & t & H2 & H3 & H4).
intros []; intuition; now right.
subst.
induction S.
-
exists (nil, t).
cbn; intuition.
eapply H4; (eauto 2).
-
edestruct IHS as [[I s'] (H1 & H3 & H5)].
intros; eapply H2; intuition.
specialize (H2 a); mp H2; lauto; destruct a; intuition.
exists (f :: I, s'); cbn; intuition try congruence.
eapply lt_nats in H2; lauto.

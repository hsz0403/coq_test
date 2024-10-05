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

Lemma end_is_var_typed Gamma A C: S = Enc C -> (repeat (alpha → alpha) (|S|) ++ Gamma ⊢(3) s : A) -> exists i e, i < |S| /\ s = var i e.
Proof using x u_neq_v t sigma N H1 EQ.
intros H2 H4; destruct end_head_var as (h' & T & s' & H5); intuition idtac; subst.
destruct T as [| t1 [| t2 T]].
+
cbn in EQ.
erewrite nth_error_sapp in EQ; (eauto 2).
rewrite nth_error_map_option in H0; destruct nth; try discriminate.
cbn in H0; injection H0 as <-.
unfold enc in EQ; Discriminate.
+
exists h'.
exists t1.
intuition.
now eapply nth_error_Some_lt in H0.
+
eapply AppR_ordertyping_inv in H4.
destruct H4 as [L]; intuition.
inv H3.
rewrite nth_error_app1, nth_error_repeated in H5; simplify in *; (eauto 2).
inv H2.
inv H8.
cbn in H5; injection H5 as ?.
rewrite !Arr_app in H; cbn in H.
eapply (f_equal arity) in H.
rewrite arity_Arr in H; cbn in H.
lia.
all: eapply nth_error_Some_lt in H0; simplify in H0; (eauto 2).

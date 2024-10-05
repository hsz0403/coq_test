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

Lemma finst_equivalence u v I W delta: I ⊆ nats (length W) -> AppR (ren delta (finst I (length W))) (Enc u v W) ≡ enc u v (concat (select I W)) (var (delta 0)).
Proof.
intros.
unfold finst.
rewrite !Lambda_ren, !AppL_ren.
rewrite !map_id_list.
2: intros ? ?; mapinj; cbn; eapply H, nats_lt in H2; now rewrite it_up_ren_lt.
cbn; rewrite it_up_ren_ge; (eauto 2); simplify.
rewrite !AppR_Lambda'; simplify; (eauto 2).
asimpl.
rewrite !sapp_ge_in; simplify; (eauto 2).
rewrite !select_variables_subst; [|simplify; (eauto 2)..].
now rewrite <-!select_map, enc_concat.

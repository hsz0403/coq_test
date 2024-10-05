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

Lemma enc_typing (Gamma: ctx) w: (Gamma ⊢(3) @var X u : alpha → alpha) -> (Gamma ⊢(3) @var X v : alpha → alpha) -> Gamma ⊢(3) enc w : alpha → alpha.
Proof.
intros.
econstructor; (eauto 2).
inv H; inv H0.
eapply AppL_ordertyping_repeated;eauto.
eapply orderlisttyping_preservation_under_renaming.
eapply repeated_ordertyping; simplify.
intros; mapinj.
eapply encb_typing.
all: eauto.
Admitted.

Lemma Enc_typing (Gamma: ctx) W: (Gamma ⊢(3) @var X u : alpha → alpha) -> (Gamma ⊢(3) @var X v : alpha → alpha) -> Gamma ⊢₊(3) Enc W : repeat (alpha → alpha) (length W).
Proof.
intros.
eapply repeated_ordertyping; simplify; (eauto 2).
intros; mapinj.
Admitted.

Lemma enc_nil s: enc [] s ≡ s.
Proof.
unfold enc; cbn.
Admitted.

Lemma enc_cons b w s: enc (b :: w) s ≡ encb b (enc w s).
Proof.
unfold enc.
eapply equiv_join; rewrite stepBeta; asimpl; eauto.
rewrite map_map, map_id_list.
rewrite map_map, map_id_list.
eauto.
Admitted.

Lemma enc_app w1 w2 s: enc (w1 ++ w2) s ≡ enc w1 (enc w2 s).
Proof.
induction w1; cbn; simplify; (eauto 2).
Admitted.

Lemma enc_concat W s: AppL (Enc W) s ≡ enc (concat W) s.
Proof.
induction W; cbn; simplify; (eauto 2).
Admitted.

Lemma encb_subst_id a (sigma: fin -> exp X): sigma u = var u -> sigma v = var v -> sigma • encb a = encb a.
Proof.
Admitted.

Lemma enc_subst_id (sigma: fin -> exp X) w: sigma u = var u -> sigma v = var v -> sigma • (enc w) = enc w.
Proof.
unfold enc.
intros H1 H2.
cbn.
f_equal.
asimpl.
f_equal.
rewrite map_id_list; (eauto 2).
intros x ?; mapinj; mapinj.
asimpl.
Admitted.

Lemma Enc_subst_id (sigma: fin -> exp X) W: sigma u = var u -> sigma v = var v -> sigma •₊ Enc W = Enc W.
Proof.
intros.
eapply map_id_list.
Admitted.

Lemma encb_eq a b: encb a ≡ encb b -> a = b.
Proof using u u_neq_v.
intros H % equiv_head_equal; cbn in *; (eauto 2).
Admitted.

Lemma encb_typing (Gamma: ctx) b: (Gamma ⊢(3) @var X u : alpha → alpha) -> (Gamma ⊢(3) @var X v : alpha → alpha) -> Gamma ⊢(3) encb b : (alpha → alpha).
Proof.
intros H1 H2.
destruct b; (eauto 2).

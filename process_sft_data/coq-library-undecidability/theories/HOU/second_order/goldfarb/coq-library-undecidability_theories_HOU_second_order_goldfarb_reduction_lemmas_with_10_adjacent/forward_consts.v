Set Implicit Arguments.
Require Import RelationClasses Morphisms Wf List Lia Init.Nat Setoid.
From Undecidability.HOU Require Import calculus.calculus unification.unification.
From Undecidability.HOU.second_order Require Export diophantine_equations goldfarb.encoding goldfarb.multiplication.
Import ListNotations.
Set Default Proof Using "Type".
Section EquationEquivalences.
Variable (sigma: fin -> exp ag).
Hypothesis (N: forall x, normal (sigma x)).
Section Variables.
End Variables.
Section Constants.
Variable (n: nat) (x: nat).
Hypothesis (Ex: encodes (sigma (F x)) n).
End Constants.
Section Addition.
Variable (m n p: nat) (x y z: nat).
Hypothesis (Ex: encodes (sigma (F x)) m) (Ey: encodes (sigma (F y)) n) (Ez: encodes (sigma (F z)) p).
End Addition.
Section Multiplication.
Variable (m n p: nat) (x y z: nat).
Hypothesis (Ex: encodes (sigma (F x)) m) (Ey: encodes (sigma (F y)) n) (Ez: encodes (sigma (F z)) p).
End Multiplication.
End EquationEquivalences.
Section Forward.
Variables (E: list deq).
Definition gf n := lambda enc n (var 0).
Definition enc_sol (sigma: nat -> nat) (x: fin) := match partition_F_G x with | inl (exist _ x _) => gf (sigma x) | inr (exist _ (x,y,z) _) => T (sigma y) (sigma x) end.
End Forward.
Section Backward.
Definition decode_subst (sigma: fin -> exp ag) (N: forall x, normal (sigma x)) (x: fin) := match dec_enc (N (F x)) with | inl (exist _ n _) => n | inr _ => 0 end.
End Backward.
Definition nileq: eq ag := (lambda lambda a, lambda lambda a).
Definition conseqs e1 e2 := match e1, e2 with | (lambda lambda s1, lambda lambda t1), (lambda lambda s2, lambda lambda t2) => (lambda lambda g s1 s2, lambda lambda g t1 t2) | _, _ => nileq end.
Notation foldeqs := (fold_right conseqs nileq).

Lemma forward_vars x n: encodes (sigma (F x)) n -> sigma • fst (varEQ x) ≡ sigma • snd (varEQ x).
Proof.
intros H.
unfold varEQ; cbn; unfold funcomp.
change shift with (add 1); rewrite ren_plus_combine, !H; cbn; unfold var_zero.
Admitted.

Lemma backward_vars x: sigma • fst (varEQ x) ≡ sigma • snd (varEQ x) -> exists n, encodes (sigma (F x)) n.
Proof using N.
cbn; simplify.
unfold funcomp; change shift with (add 1); rewrite ren_plus_combine; unfold var_zero; cbn.
Admitted.

Lemma backward_consts: sigma • fst (constEQ x) ≡ sigma • snd (constEQ x) -> n = 1.
Proof using Ex.
cbn.
unfold funcomp; change shift with (add 1); rewrite ren_plus_combine; unfold var_zero; cbn.
rewrite Ex.
asimpl.
intros ? % equiv_lam_elim % equiv_lam_elim.
Admitted.

Lemma forward_add: m + n = p -> sigma • fst (addEQ x y z) ≡ sigma • snd (addEQ x y z).
Proof using Ex Ey Ez.
intros <-; cbn.
unfold funcomp; change shift with (add 1); rewrite !ren_plus_combine; unfold var_zero; cbn.
Admitted.

Lemma backward_add: sigma • fst (addEQ x y z) ≡ sigma • snd (addEQ x y z) -> m + n = p.
Proof using Ex Ey Ez.
cbn.
unfold funcomp; change shift with (add 1); rewrite !ren_plus_combine; unfold var_zero; cbn.
rewrite Ex, Ey, Ez; simplify; intros H % equiv_lam_elim % equiv_lam_elim.
rewrite <-enc_app in H.
Admitted.

Lemma forward_mul: m * n = p -> sigma (G x y z) = T n m -> sigma • fst (mulEQ x y z) ≡ sigma • snd (mulEQ x y z).
Proof using Ex Ey Ez.
intros H1 H2.
unfold mulEQ; cbn.
unfold funcomp.
rewrite H2.
change shift with (add 1); rewrite !ren_plus_combine; cbn [plus].
rewrite Ex, Ey, Ez.
subst p.
Admitted.

Lemma backward_mult: sigma • fst (mulEQ x y z) ≡ sigma • snd (mulEQ x y z) -> m * n = p /\ sigma (G x y z) = T n m.
Proof using N Ex Ey Ez.
unfold mulEQ; cbn.
unfold funcomp.
change shift with (add 1); rewrite !ren_plus_combine; cbn [plus].
rewrite Ex, Ey, Ez.
intros H.
Admitted.

Lemma tab_typing {X} n (f: nat -> exp X) g k Gamma: (forall i, Gamma ⊢(n) f i : g i) -> Gamma ⊢₊(n) tab f k : tab g k.
Proof.
intros; induction k; cbn; (eauto 2).
Admitted.

Lemma gf_typing Gamma n: Gamma ⊢(2) gf n : alpha → alpha.
Proof.
econstructor.
eapply enc_typing.
Admitted.

Lemma GT_typing Gamma m n: Gamma ⊢(2) T n m : alpha → alpha → alpha → alpha.
Proof.
do 3 econstructor.
eapply lin_typing; [|eauto].
rewrite repeated_tab.
simplify.
eapply tab_typing.
intros; econstructor; cbn.
econstructor.
Admitted.

Lemma enc_sol_encodes theta h: encodes (enc_sol theta (F h)) (theta h).
Proof.
unfold enc_sol.
destruct partition_F_G as [[x ?]|[((x,y),z) ?]].
-
eapply F_injective in e as ->.
intros t delta.
unfold gf.
cbn; rewrite stepBeta; asimpl; (eauto 2).
-
Admitted.

Lemma enc_sol_T theta x y z: (enc_sol theta (G x y z)) = T (theta y) (theta x).
Proof.
unfold enc_sol.
destruct partition_F_G as [[x' ?]|[((x',y'),z') ?]].
-
exfalso; eapply disjoint_F_G; (eauto 2).
-
Admitted.

Lemma forward_consts: n = 1 -> sigma • fst (constEQ x) ≡ sigma • snd (constEQ x).
Proof using Ex.
cbn; unfold funcomp; change shift with (add 1); rewrite ren_plus_combine; unfold var_zero; cbn.
rewrite Ex; asimpl; now intros ->.

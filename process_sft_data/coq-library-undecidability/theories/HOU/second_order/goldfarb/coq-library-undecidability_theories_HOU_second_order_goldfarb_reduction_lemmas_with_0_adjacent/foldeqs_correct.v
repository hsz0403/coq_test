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

Lemma foldeqs_correct sigma E: (forall s1 s2, (s1, s2) ∈ E -> (exists t, s1 = lambda lambda t) /\ (exists t, s2 = lambda lambda t)) -> (sigma •₊ left_side E) ≡₊ (sigma •₊ right_side E) <-> (sigma • fst (foldeqs E) ≡ sigma • snd (foldeqs E)).
Proof.
induction E as [| [s t]]; simplify.
-
cbn; firstorder.
-
intros H.
apply id in H as H'.
specialize (H' s t) as ([t1 H1]&[t2 H2]); lauto; subst.
cbn.
specialize (foldeqs_lambda_lambda E) as (u&v&H'); rewrite H' in *.
mp IHE; (eauto 2).
intros; eapply H; firstorder.
cbn in IHE.
cbn; unfold left_side, right_side in *.
split; [intros [H1 H2] % equiv_lstep_cons_inv| intros H1]; do 2 eapply equiv_lam_elim in H1.
+
destruct IHE as [IHE _]; rewrite H1; mp IHE; (eauto 1); do 2 eapply equiv_lam_elim in IHE; now rewrite IHE.
+
Injection H1.
Injection H0.
rewrite H3.
destruct IHE as [_ ->]; (eauto 2).
now rewrite H2.

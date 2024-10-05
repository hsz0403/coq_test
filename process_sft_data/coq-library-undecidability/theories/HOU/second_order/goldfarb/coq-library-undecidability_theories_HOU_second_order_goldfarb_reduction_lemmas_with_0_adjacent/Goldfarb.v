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

Lemma Goldfarb : H10 ⪯ OU 2 ag.
Proof.
unshelve eexists.
-
intros E.
unshelve econstructor.
exact (Gamma__deq E).
1: eapply fst.
2: eapply snd.
1 - 2: eapply foldeqs, (H10_to_SOU E).
exact (alpha → alpha → alpha).
all: eapply foldeqs_typing; cbn -[Gamma__deq].
all: eapply H10_to_SOU.
-
intros E.
split.
+
intros H % H10_SU.
destruct H as (Delta & sigma & H1 & H2).
exists Delta.
exists sigma.
intuition.
eapply foldeqs_correct, equiv_pointwise_eqs; (eauto 2).
cbn.
intros s1 s2 (d&H3&H4) % in_flat_map.
destruct d; cbn in H4; intuition.
all: change s1 with (fst (s1, s2)); rewrite <-?H, <-?H0.
all: change s2 with (snd (s1, s2)); rewrite <-?H, <-?H0.
all: cbn; (eauto 2).
+
intros (Delta & sigma & T & EQ).
eapply SU_H10.
exists Delta, sigma.
intuition.
eapply equiv_eqs_pointwise; (eauto 1); eapply foldeqs_correct; (eauto 2).
cbn.
intros s1 s2 (d&H3&H4) % in_flat_map.
destruct d; cbn in H4; intuition.
all: change s1 with (fst (s1, s2)); rewrite <-?H1, <-?H0.
all: change s2 with (snd (s1, s2)); rewrite <-?H1, <-?H0.
all: cbn; (eauto 2).

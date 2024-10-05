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

Lemma enc_characteristic X (s: exp X): normal s -> lambda lambda (var 0) ((ren (shift >> shift) s) (var 1) (var 0)) ≡ lambda lambda (ren (shift >> shift) s) ((var 0) (var 1)) (var 0) -> exists n, s = enc n.
Proof.
intros N; apply normal_nf in N as N'.
induction N' as [k a t T _ _ isA ->].
intros H'; Injection H'.
clear H'.
Injection H.
clear H.
rename H0 into H.
asimpl in H.
destruct k as [|[|[]]]; cbn in H.
-
eapply equiv_app_elim in H; intuition.
symmetry in H1; eapply equiv_neq_var_app in H1 as [].
all: cbn; simplify; destruct a; cbn in isA; eauto.
-
do 2 (rewrite stepBeta in H; asimpl; eauto).
eapply equiv_app_elim in H; intuition.
symmetry in H1; eapply equiv_neq_var_app in H1 as [].
all: cbn; simplify; destruct a as [[] | | |]; cbn in isA; eauto.
-
rewrite <-AppR_subst in H.
remember (AppR a T) as t.
clear isA a T Heqt.
do 4 (rewrite stepBeta in H; asimpl; cbn; asimpl; eauto).
rewrite idSubst_exp in H; [|intros [|[]]; cbn; eauto].
eapply normal_Lambda in N.
pose (sigma := @var X 0 .: var 0 (var 1) .: shift >> (shift >> var)).
fold sigma in H.
enough (exists n, t = AppL (repeat (var 0) n) (var 1)) as [n ->] by now (exists n).
induction t as [[| [|]] | | |]; cbn in H; try solve [unfold funcomp in H; Discriminate].
+
exists 0; reflexivity.
+
eapply head_atom in N as isA; eauto.
eapply equiv_app_elim in H as [EQ1 EQ2]; eauto.
2: eapply atom_head_lifting; eauto.
2: intros [| [| []]]; cbn; eauto.
destruct t1 as [[| [|]] | | |]; cbn in EQ1; try Discriminate.
*
mp IHt2; [eauto using normal_app_r|].
specialize (IHt2 EQ2).
destruct IHt2 as [n IHt2]; exists (S n); cbn; now rewrite IHt2.
*
unfold funcomp in EQ1; Injection EQ1.
discriminate.
*
eapply equiv_neq_var_app in EQ1 as [].
eapply atom_head_lifting; eauto.
intros [| [| []]]; cbn; eauto.
-
repeat (rewrite stepBeta in H; cbn; asimpl; eauto).
Discriminate.

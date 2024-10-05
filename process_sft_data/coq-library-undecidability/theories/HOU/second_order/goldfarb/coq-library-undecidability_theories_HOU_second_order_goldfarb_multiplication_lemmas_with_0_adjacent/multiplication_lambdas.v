Set Implicit Arguments.
Require Import List Lia Program.Program.
From Undecidability.HOU Require Import std.std axioms.
Require Import RelationClasses Morphisms Wf Init.Nat Setoid.
From Undecidability.HOU Require Import calculus.calculus second_order.goldfarb.encoding.
Require Import FinFun Coq.Arith.Wf_nat.
Import ListNotations.
Set Default Proof Using "Type".
Section Multiplication.
Variable (n: nat).
Implicit Type (X Y: list (nat * nat)).
Hint Rewrite Cons_subst : asimpl.
Hint Rewrite Pair_subst : asimpl.
Notation r := (var 2).
Notation A := (var 1).
Notation B := (var 0).
Let σ p q := B .: A .: ⟨enc p A, enc q B⟩ ::: Nil .: (add 2) >> var.
Let τ := Succ B .: enc n A .: Nil .:((add 2) >> var).
Definition t k := ⟨enc (k * n) A, enc k B⟩.
Definition T k := lambda lambda lambda lin (tab t k) r.
Hint Rewrite T_subst T_ren : asimpl.
Section G_subst.
End G_subst.
Section t_subst.
End t_subst.
Hint Rewrite hat_t_sigma hat_t_tau : asimpl.
Section G_reduce.
End G_reduce.
Definition Grel m p G := lambda lambda (ren (add 2) G) (⟨ enc p A, enc m B⟩ ::: Nil) A B ≡ lambda lambda ⟨ A, B ⟩ ::: (ren (add 2) G) Nil (enc n A) (Succ B).
Section InvertSubstitution.
Variable (p q: nat).
End InvertSubstitution.
Section RecoverStructure.
Fixpoint size_exp {Z} (s: exp Z) := match s with | var _ => 0 | const c => 0 | app s t => S (size_exp s + size_exp t) | lambda s => S (size_exp s) end.
End RecoverStructure.
End Multiplication.

Lemma multiplication_lambdas M m p: normal M -> Grel m p M -> (exists M', M = (lambda lambda lambda M') /\ σ p m • M' = t 0 ::: (τ • M')).
Proof.
unfold Grel, Pair, Cons.
cbn.
intros Nu EQ.
remember (fun m : nat => S (S m)) as delta.
rename M into u.
assert (normal (ren delta u)) as N' by (subst; eapply normal_ren; eauto).
do 2 apply equiv_lam_elim in EQ.
destruct u as [| | u' | ]; unfold funcomp; cbn in EQ.
4: eapply head_atom in N'; eauto.
1, 2, 4: Injection EQ; Injection H; Discriminate.
rewrite stepBeta in EQ; eauto.
asimpl in EQ.
rewrite stepBeta in EQ; eauto.
asimpl in EQ.
destruct u' as [[]| | u' | ]; cbn in EQ.
1 - 3: Injection EQ; Injection H; Discriminate.
-
do 2 (rewrite stepBeta in EQ; eauto; asimpl in EQ; cbn in EQ).
destruct u' as [[|[]] | | u' | u1 u2 ]; cbn in EQ.
1 - 4: Injection EQ; unfold funcomp in *; Discriminate.
+
exists u'.
intuition.
do 2 (rewrite stepBeta in EQ; eauto; asimpl in EQ; cbn in EQ).
repeat eapply normal_lam_elim in Nu.
eapply equiv_unique_normal_forms; [eauto | eauto |idtac..].
subst delta; exact EQ.
2: eapply normal_app_intro; cbn; intuition.
2: repeat eapply normal_app_intro; eauto.
all: eapply normal_subst; try eassumption.
all: intros [|[|[]]]; cbn; eauto 2.
all: unfold funcomp, Nil; (repeat eapply normal_app_intro); eauto 2.
destruct n; simplify; eauto.
+
exfalso.
repeat eapply normal_lam_elim in Nu.
eapply head_atom in Nu as H'; eauto.
eapply atom_head_lifting with (sigma := A .: g (g (enc p A) (enc m B)) (id Nil) .: delta >> var) in H' as H4.
2: intros [|[]]; cbn; eauto.
cbn in H4.
Injection EQ.
Injection H.
destruct u1 as [[|[]]|[]| |]; cbn in H1; try Injection EQ; try Discriminate.
-
eapply normal_lam_elim in Nu.
eapply head_atom in Nu; eauto.
eapply atom_head_lifting with (sigma := g (g (enc p A) (enc m B)) Nil .: delta >> var) in Nu; cbn in Nu.
2: intros []; cbn; eauto.
Injection EQ.
Injection H.
Discriminate.

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

Lemma step_u u p q k: σ p q • u = t k ::: (τ • u) -> u = r \/ (exists u', u = t k ::: u').
Proof.
intros EQ.
destruct u as [| | | t1 t3]; try discriminate; eauto.
-
cbn in *.
asimpl in EQ.
destruct f as [|[|[]]]; try discriminate.
now left.
-
destruct t1 as [[|[|[]]]| | | t1 t2]; cbn in *; try discriminate; eauto.
destruct t1 as [[|[|[]]]| [] | |]; cbn in *; try discriminate; eauto.
injection EQ as EQ1 EQ2.
intros.
asimpl in EQ1.
eapply subst_t in EQ1; subst; eauto.
right.
now (exists t3).

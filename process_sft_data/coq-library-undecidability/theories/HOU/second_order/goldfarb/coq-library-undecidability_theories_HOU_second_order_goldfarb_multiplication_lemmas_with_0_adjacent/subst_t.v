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

Lemma subst_t e k: σ p q • e = t k -> e = t k.
Proof.
unfold t; intros.
destruct e as [ [| [| []]] | | | e1 e3 ] ; try discriminate.
{
cbn in *.
asimpl in H.
cbn in *.
injection H as ?.
destruct k; discriminate.
}
destruct e1 as [ [| [| []]] | | | e1 e2 ]; try discriminate.
destruct e1 as [ [| [| []]] | [] | | ]; try discriminate.
cbn -[add] in *.
f_equal; injection H as H H'.
asimpl in H.
asimpl in H'.
cbn in H, H'.
unfold funcomp in H, H'.
eapply subst_enc in H as [? []]; eauto.
eapply subst_enc in H' as [? []]; eauto.
subst.
eapply subst_var_a in H0.
eapply subst_var_b in H2.
now subst.

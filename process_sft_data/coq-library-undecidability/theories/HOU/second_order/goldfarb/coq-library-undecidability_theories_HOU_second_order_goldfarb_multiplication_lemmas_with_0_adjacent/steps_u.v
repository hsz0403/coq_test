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

Lemma steps_u u p q k: σ p q • u = t k ::: (τ • u) -> exists l, u = lin (tab (fun i => t (i + k)) l) r.
Proof.
specialize (well_founded_ind (measure_wf lt_wf (@size_exp ag))) as ind.
revert k.
induction u as [u IH] using ind; intros k EQ.
destruct (step_u _ _ _ EQ) as [H1|H1].
-
subst.
exists 0.
reflexivity.
-
destruct H1 as [u' H1].
rewrite H1 in EQ.
rewrite !Cons_subst in EQ.
asimpl in EQ.
eapply Cons_injective in EQ as [_ EQ].
eapply IH in EQ as [l]; [|subst u; hnf; cbn; lia].
exists (S l).
rewrite tab_S, H1, H.
simplify.
unfold Cons.
f_equal.
f_equal.
rewrite !tab_map_nats.
eapply map_ext.
intros.
f_equal; lia.

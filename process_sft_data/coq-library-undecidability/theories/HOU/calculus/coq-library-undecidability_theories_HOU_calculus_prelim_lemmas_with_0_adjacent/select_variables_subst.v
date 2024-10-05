Set Implicit Arguments.
Require Import List Arith Lia Morphisms.
Import ListNotations.
From Undecidability.HOU Require Export std.std.
From Undecidability.HOU Require Import calculus.terms.
Fixpoint sapp {X} (A: list X) (sigma: fin -> X): fin -> X := match A with | nil => sigma | a :: A => a .: sapp A sigma end.
Notation "A .+ sigma" := (sapp A sigma) (at level 67, right associativity).
Hint Resolve max_le_left max_le_right : core.
Definition dom X (A: list X) := nats (length A).
Hint Rewrite dom_length dom_map: simplify.
Hint Resolve <-dom_lt_iff : core.
Ltac domin H := match type of H with | nth _ _ = _ => eapply dom_nth in H as ? | _ ∈ dom _ => eapply dom_in in H as [y H]; rewrite ?H end.
Hint Resolve nth_error_In : core.
Hint Resolve le_plus_r le_plus_l : core.
Hint Resolve Max.max_lub : core.
Hint Resolve Nat.le_succ_diag_r le_Sn_le : core.
Hint Rewrite Nat.max_lub_iff Max.max_0_r Max.max_0_l: simplify.
Hint Rewrite Nat.mul_0_r Nat.mul_succ_r Nat.mul_0_l Nat.mul_succ_l: simplify.
Hint Rewrite Nat.add_succ_r : simplify.
Arguments exp : clear implicits.
Coercion app : exp >-> Funclass.
Notation "'lambda' s" := (lam s) (at level 65, right associativity).
Arguments var_exp {_} _.
Notation var := var_exp.
Notation "A → B" := (arr A B) (at level 65, right associativity).
Coercion typevar : nat >-> type.
Definition alpha : type := 0.
Notation "gamma • s" := (subst_exp gamma s) (at level 69, right associativity).
Notation ren := ren_exp.
Notation up := up_exp_exp.

Lemma select_variables_subst X S I sigma: I ⊆ nats (length S) -> map (subst_exp (S .+ sigma)) (map (@var_exp X) I) = select I S.
Proof.
intros.
rewrite map_map; cbn.
induction I; cbn; eauto.
destruct (nth_error S a) eqn: H1.
+
rewrite IHI; firstorder.
f_equal.
now eapply nth_error_sapp.
+
exfalso.
apply nth_error_None in H1.
specialize (H a).
mp H; [now left|].
eapply nats_lt in H.
lia.

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

Lemma ren_comp X delta delta' s: @ren_exp X delta (ren_exp delta' s) = ren_exp (delta' >> delta) s.
Proof.
asimpl.
reflexivity.

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

Lemma sapp_app X (A B: list X) sigma: (A ++ B) .+ sigma = A .+ B .+ sigma.
Proof.
induction A; cbn; eauto.
Admitted.

Lemma nth_error_sapp X L (x: X) n sigma: nth_error L n = Some x -> (L .+ sigma) n = x.
Proof.
induction L in n |-*; cbn.
+
destruct n; cbn in *; discriminate.
+
firstorder.
destruct n; cbn in *.
congruence.
Admitted.

Lemma sapp_lt_in X x (A: list X) sigma: x < length A -> (A .+ sigma) x ∈ A.
Proof.
intros H.
eapply nth_error_In with (n := x).
eapply nth_error_lt_Some in H as [a].
Admitted.

Lemma sapp_ge_in X x (A: list X) sigma: length A <= x -> sapp A sigma x = sigma (x - length A).
Proof.
induction A in x |-*.
-
cbn.
intros _.
destruct x; reflexivity.
-
intros H.
destruct x.
inv H.
Admitted.

Lemma ren_plus_base (X: Const): @ren_exp X shift = ren_exp (plus 1).
Proof.
Admitted.

Lemma ren_comp X delta delta' s: @ren_exp X delta (ren_exp delta' s) = ren_exp (delta' >> delta) s.
Proof.
asimpl.
Admitted.

Lemma it_up_ren_spec n delta x: it n up_ren delta x = if dec2 lt x n then x else n + delta (x - n).
Proof.
induction n in x, delta |-*; cbn.
-
destruct dec2; intuition.
lia.
-
destruct x; cbn; destruct dec2; intuition.
lia.
all: unfold funcomp; erewrite IHn.
Admitted.

Lemma it_up_ren_lt n delta x: x < n -> it n up_ren delta x = x.
Proof.
Admitted.

Lemma it_up_ren_ge n delta x: x >= n -> it n up_ren delta x = n + delta (x - n).
Proof.
Admitted.

Lemma it_up_spec X n (sigma: fin -> @exp X) x: it n up_exp_exp sigma x = if dec2 lt x n then var_exp x else ren_exp (plus n) (sigma (x - n)).
Proof.
induction n in x, sigma |-*; cbn.
-
asimpl; destruct dec2; [lia|]; now destruct x.
-
destruct x; cbn; destruct dec2; intuition; [lia| |].
all: unfold funcomp; erewrite IHn.
Admitted.

Lemma it_up_lt X n (sigma: fin -> @exp X) x: x < n -> it n up_exp_exp sigma x = var_exp x.
Proof.
Admitted.

Lemma it_up_ge X n (sigma: fin -> @exp X) x: x >= n -> it n up_exp_exp sigma x = ren_exp (plus n) (sigma (x - n)).
Proof.
Admitted.

Lemma it_up_var_sapp X A n delta e: (forall x, delta x >= x) -> n = length A -> subst_exp (A .+ var_exp) (ren_exp (it n up_ren delta) e) = subst_exp (A .+ delta >> @var_exp X) e.
Proof.
intros; subst.
asimpl.
eapply ext_exp.
intros; unfold funcomp.
assert (x < length A \/ x >= length A) as [] by lia.
+
rewrite it_up_ren_lt; eauto.
eapply nth_error_lt_Some in H0 as [a].
erewrite !nth_error_sapp; eauto.
+
rewrite it_up_ren_ge; simplify; eauto.
erewrite !sapp_ge_in; simplify; eauto.
Admitted.

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
Admitted.

Lemma max_le_left n m: n <= max n m.
Proof.
Admitted.

Lemma max_le_right n m: m <= max n m.
Proof.
Admitted.

Lemma ren_plus_combine X n m s: @ren_exp X (plus n) (ren_exp (plus m) s) = ren_exp (plus (n + m)) s.
Proof.
rewrite ren_comp.
f_equal.
induction n; cbn; fext; intros; cbn.
+
reflexivity.
+
rewrite <-IHn.
reflexivity.

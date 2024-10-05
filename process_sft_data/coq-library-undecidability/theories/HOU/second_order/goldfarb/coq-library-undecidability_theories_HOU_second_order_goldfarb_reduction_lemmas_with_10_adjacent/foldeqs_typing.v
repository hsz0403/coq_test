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

Lemma enc_sol_encodes theta h: encodes (enc_sol theta (F h)) (theta h).
Proof.
unfold enc_sol.
destruct partition_F_G as [[x ?]|[((x,y),z) ?]].
-
eapply F_injective in e as ->.
intros t delta.
unfold gf.
cbn; rewrite stepBeta; asimpl; (eauto 2).
-
Admitted.

Lemma enc_sol_T theta x y z: (enc_sol theta (G x y z)) = T (theta y) (theta x).
Proof.
unfold enc_sol.
destruct partition_F_G as [[x' ?]|[((x',y'),z') ?]].
-
exfalso; eapply disjoint_F_G; (eauto 2).
-
Admitted.

Lemma typing_forward sigma: (sigma ⊢⁺ₑ E) -> [] ⊩(2) enc_sol sigma : Gamma__deq E.
Proof.
eauto; intros ????; unfold enc_sol.
destruct partition_F_G as [[]|[((x & y) & z) ?]]; subst.
+
eapply nth_Gamma__deq_F in H0 as ->.
eapply gf_typing.
+
eapply nth_Gamma__deq_G in H0 as ->.
Admitted.

Lemma H10_SU: H10 E -> SOU ag 2 (H10_to_SOU E).
Proof.
intros [sigma H].
exists [].
exists (enc_sol sigma).
split.
now eapply typing_forward.
intros s t; change s with (fst (s,t)) at 2; change t with (snd (s,t)) at 3.
remember (s,t) as e.
clear Heqe s t.
intros H'; cbn in *.
eapply in_Equations in H' as (d & ? & ?).
destruct d; cbn in *; intuition idtac; subst.
all: try eapply forward_add.
all: try eapply forward_consts.
all: try eapply forward_mul.
all: try eapply forward_vars.
all: try eapply enc_sol_encodes.
all: eapply H in H0; inv H0; (eauto 2).
Admitted.

Lemma decode_subst_encodes (sigma: fin -> exp ag) N x n: encodes (sigma (F x)) n -> decode_subst sigma N x = n.
Proof.
intros H; unfold decode_subst.
destruct dec_enc as [[m H1]|H1].
-
specialize (H a id); asimpl in H.
rewrite H in H1.
eapply enc_injective in H1 as []; (eauto 2).
-
exfalso.
eapply H1.
exists n.
specialize (H a id); asimpl in H.
Admitted.

Lemma SU_H10 E: SOU ag 2 (H10_to_SOU E) -> H10 E.
Proof.
rewrite SOU_NSOU; (eauto 2).
intros (Delta & sigma & T & EQ & N).
exists (decode_subst sigma N).
intros e H; pose (Q := eqs e).
assert (forall p, p ∈ Q -> sigma • fst p ≡ sigma • snd p) as EQs; [|clear EQ].
-
intros [s t] G.
eapply EQ.
eapply in_Equations.
eauto.
-
destruct e; econstructor; cbn in Q, EQs.
all: specialize (EQs (varEQ x)) as EQx; mp EQx; intuition idtac; eapply backward_vars in EQx as [n EQx]; (eauto 2).
2 - 3: specialize (EQs (varEQ y)) as EQy; mp EQy; intuition idtac; eapply backward_vars in EQy as [m EQy]; (eauto 2).
2 - 3: specialize (EQs (varEQ z)) as EQz; mp EQz; intuition idtac; eapply backward_vars in EQz as [p EQz]; (eauto 2).
all: repeat (erewrite decode_subst_encodes;[|eauto]).
+
eapply backward_consts; (eauto 4).
+
eapply backward_add; (eauto 1); eapply EQs; (eauto 5).
+
Admitted.

Lemma Goldfarb': H10 ⪯ SOU ag 2.
Proof.
exists H10_to_SOU; intros x; split.
-
eapply H10_SU.
-
Admitted.

Lemma conseqs_combine sigma s1 s2 t1 t2: sigma • (lambda lambda s1) ≡ sigma • (lambda lambda t1) /\ sigma • (lambda lambda s2) ≡ sigma • (lambda lambda t2) <-> sigma • (lambda lambda g s1 s2) ≡ sigma • (lambda lambda g t1 t2).
Proof.
cbn; split.
-
intros [H1 H2]; do 2 (eapply equiv_lam_elim in H1; eapply equiv_lam_elim in H2).
now rewrite H1, H2.
-
intros H1; do 2 eapply equiv_lam_elim in H1.
Injection H1.
Injection H.
Admitted.

Lemma foldeqs_lambda_lambda E: exists s t, foldeqs E = (lambda lambda s, lambda lambda t).
Proof.
induction E as [|[s t]]; cbn; (eauto 2).
-
do 2 eexists; reflexivity.
-
destruct IHE as (s'&t'&IH).
do 2 (destruct s; try solve [do 2 eexists; reflexivity]).
do 2 (destruct t; try solve [do 2 eexists; reflexivity]).
Admitted.

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
Admitted.

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
Admitted.

Lemma foldeqs_typing Gamma E: Gamma ⊢₊₊(2) E : repeat (alpha → alpha → alpha) (length E) -> Gamma ⊢₂(2) (foldeqs E) : alpha → alpha → alpha.
Proof.
remember (repeat (alpha → alpha → alpha) (| E |)) as L.
induction 1 in HeqL |- *; cbn.
-
repeat econstructor.
-
do 2 (destruct s; try solve [repeat econstructor]).
do 2 (destruct t; try solve [repeat econstructor]).
specialize (foldeqs_lambda_lambda E) as (u&v&H'); rewrite H' in *.
cbn in HeqL.
injection HeqL as -> ->.
mp IHeqs_ordertyping; (eauto 2).
inv H0.
inv H4.
inv H.
inv H4.
destruct IHeqs_ordertyping as [T1 T2].
inv T1.
inv H4.
inv T2.
inv H4.
repeat econstructor; (eauto 2).

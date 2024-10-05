From Undecidability.L Require Export Util.L_facts.
Require Import Coq.Logic.ConstructiveEpsilon.
Import L_Notations.
Hint Resolve eval_converges : core.
Inductive seval : nat -> term -> term -> Prop := | sevalR n s : seval n (lam s) (lam s) | sevalS n s t u v w : seval n s (lam u) -> seval n t (lam v) -> seval n (subst u 0 (lam v)) w -> seval (S n) (s t) w.
Local Notation "s '⇓' n t" := (seval n s t) (at level 51).
Hint Resolve seval_eval : core.
Fixpoint eva (n : nat) (u : term) := match u with | var n => None | lam s => Some (lam s) | app s t => match n with | 0 => None | S n => match eva n s, eva n t with | Some (lam s), Some t => eva n (subst s 0 t) | _ , _ => None end end end.
Require Import Coq.Logic.ConstructiveEpsilon.
Definition cChoice := constructive_indefinite_ground_description_nat_Acc.
Fixpoint stepf (s : term) : list term := match s with | (lam _) => [] | var x => [] | app (lam s) (lam t) => [subst s 0 (lam t)] | app s t => map (fun x => app x t) (stepf s) ++ map (fun x => app s x) (stepf t) end.
Ltac stepf_tac := match goal with | [ H : app _ _ ≻ ?t |- ?P ] => inv H | [ H : var _ ≻ ?t |- ?P ] => inv H | [ H : lam _ ≻ ?t |- ?P ] => inv H | [ H : exists x, _ |- _ ] => destruct H | [ H : _ /\ _ |- _ ] => destruct H end + subst.
Fixpoint stepn (n : nat) s : list term := match n with | 0 => [s] | S n => flat_map (stepn n) (stepf s) end.

Lemma seval_eval n s t : seval n s t -> eval s t.
Proof with eauto using star_trans, star_trans_l, star_trans_r.
intros.
induction H as [ | n s t u v w _ [IHe1 _] _ [IHe2 _] _ [IHe3 lam_w]].
-
repeat econstructor.
-
split...
transitivity ((lam u) t)...
transitivity ((lam u) (lam v))...
Admitted.

Lemma seval_S n s t : seval n s t -> seval (S n) s t.
Proof.
Admitted.

Lemma eval_step s s' t n : s ≻ s' -> seval n s' t -> seval (S n) s t.
Proof with eauto using seval_S, seval.
intros H; revert n t; induction H; intros n u A...
-
inv A...
-
Admitted.

Lemma eval_seval s t : eval s t -> exists n, seval n s t.
Proof.
intros [A B].
induction A.
-
destruct B.
subst.
eauto using seval.
-
destruct (IHA B) as [k C].
eauto using seval, eval_step.
Grab Existential Variables.
Admitted.

Lemma eva_lam n s t : eva n s = Some t -> lambda t.
Proof.
revert s t; induction n; intros s t H; destruct s; try inv H; eauto.
destruct (eva n s1) eqn:Hs1; try now inv H1.
destruct t0; try inv H1.
destruct (eva n s2); try inv H0.
eapply IHn in H1.
Admitted.

Lemma eva_seval n s t : eva n s = Some t -> seval n s t.
Proof.
revert s t.
induction n; intros s t H; destruct s; try now inv H; eauto using seval.
destruct (eva n s1) eqn:Hs1; try now (simpl in H; rewrite Hs1 in H; inv H).
destruct t0; try now (simpl in H; rewrite Hs1 in H; inv H).
destruct (eva n s2) eqn:Hs2; try now (simpl in H; rewrite Hs1, Hs2 in H; inv H).
destruct (eva_lam Hs2); subst t1.
econstructor; eauto.
eapply IHn.
simpl in H.
rewrite Hs1, Hs2 in H.
Admitted.

Lemma seval_eva n s t : seval n s t -> eva n s = Some t.
Proof.
induction 1.
-
destruct n; reflexivity.
-
simpl.
rewrite IHseval1, IHseval2.
Admitted.

Lemma eva_seval_iff n s t : eva n s = Some t <-> seval n s t.
Proof.
Admitted.

Lemma equiv_eva s t : lambda t -> s == t -> exists n, eva n s = Some t.
Proof.
intros lt A.
cut (eval s t).
intros H.
eapply eval_seval in H.
destruct H as [n H].
eapply seval_eva in H.
eauto.
Admitted.

Lemma eva_equiv s s' n : eva n s = Some s' -> s == s'.
Proof.
intros H.
eapply eva_seval in H.
eapply seval_eval in H.
destruct H.
eapply star_equiv.
Admitted.

Lemma eval_converges s t : eval s t -> converges s.
Proof.
intros [v [R lv]].
exists t.
rewrite v.
subst.
split.
reflexivity.
auto.

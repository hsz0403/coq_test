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

Lemma seval_rect (P : nat -> term -> term -> Type) (HR : forall (n : nat) (s : term), P n (lam s) (lam s)) (HS : forall (n : nat) (s t u v w : term), seval n s (lam u) -> P n s (lam u) -> seval n t (lam v) -> P n t (lam v) -> seval n (subst u 0 (lam v)) w -> P n (subst u 0 (lam v)) w -> P (S n) (s t) w): forall n s t, seval n s t -> P n s t.
Proof.
intros n.
induction n as [n IHn]using lt_wf_rect.
intros s t H'.
eapply seval_eva in H'.
destruct n.
{
cbn in H'.
destruct s;inv H'.
easy.
}
cbn in H'.
destruct s.
1,3:now inv H'.
destruct eva eqn:H1.
2:easy.
destruct t0.
1,2:easy.
destruct eva eqn:H2 in H'.
2:easy.
specialize (eva_lam H2) as H''.
destruct t1.
1,2:now exfalso;inversion H''.
clear H''.
specialize (eva_lam H') as H''.
destruct t.
1,2:now exfalso;inversion H''.
eapply HS.
all:eauto using eva_seval.

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

Lemma eva_Sn_n n s : eva (S n) s = None -> eva n s = None.
Proof.
intros H; destruct s, n; try reflexivity; try now inv H.
simpl.
destruct (eva n s1) eqn:Hs1, (eva n s2) eqn:Hs2.
-
destruct t; try reflexivity.
assert (Hs' : eva (S n) s1 = Some (lam t)) by eauto using eva_n_Sn.
assert (Ht' : eva (S n) s2 = Some (t0)) by eauto using eva_n_Sn.
destruct (eva n (subst t 0 t0)) eqn:Ht; try reflexivity.
assert (H' : eva (S n) (subst t 0 t0) = Some t1) by eauto using eva_n_Sn.
rewrite <- H.
change (Some t1 = match eva (S n) s1, eva (S n) s2 with | Some (lam s), Some t => eva (S n) (subst s 0 t) | _ , _ => None end).
rewrite Hs', Ht'.
rewrite H'.
reflexivity.
-
destruct t; reflexivity.
-
reflexivity.
-
reflexivity.

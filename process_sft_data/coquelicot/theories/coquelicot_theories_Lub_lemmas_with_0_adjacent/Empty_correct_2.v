Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Markov.
Open Scope R_scope.
Definition is_ub_Rbar (E : R -> Prop) (l : Rbar) := forall (x : R), E x -> Rbar_le x l.
Definition is_lb_Rbar (E : R -> Prop) (l : Rbar) := forall (x : R), E x -> Rbar_le l x.
Definition is_lub_Rbar (E : R -> Prop) (l : Rbar) := is_ub_Rbar E l /\ (forall b, is_ub_Rbar E b -> Rbar_le l b).
Definition is_glb_Rbar (E : R -> Prop) (l : Rbar) := is_lb_Rbar E l /\ (forall b, is_lb_Rbar E b -> Rbar_le b l).
Definition Lub_Rbar (E : R -> Prop) := proj1_sig (ex_lub_Rbar E).
Definition Glb_Rbar (E : R -> Prop) := proj1_sig (ex_glb_Rbar E).
Definition Rbar_is_upper_bound (E : Rbar -> Prop) (l : Rbar) := forall x, E x -> Rbar_le x l.
Definition Rbar_is_lower_bound (E : Rbar -> Prop) (l : Rbar) := forall x, E x -> Rbar_le l x.
Definition Rbar_is_lub (E : Rbar -> Prop) (l : Rbar) := Rbar_is_upper_bound E l /\ (forall b : Rbar, Rbar_is_upper_bound E b -> Rbar_le l b).
Definition Rbar_is_glb (E : Rbar -> Prop) (l : Rbar) := Rbar_is_lower_bound E l /\ (forall b : Rbar, Rbar_is_lower_bound E b -> Rbar_le b l).
Definition Rbar_lub (E : Rbar -> Prop) := proj1_sig (Rbar_ex_lub E).
Definition Rbar_glb (E : Rbar -> Prop) := proj1_sig (Rbar_ex_glb E).
Definition Empty (E : R -> Prop) := Lub_Rbar (fun x => x = 0 \/ E x) = Glb_Rbar (fun x => x = 0 \/ E x) /\ Lub_Rbar (fun x => x = 1 \/ E x) = Glb_Rbar (fun x => x = 1 \/ E x).

Lemma Empty_correct_2 (E : R -> Prop) : (forall x, ~ E x) -> Empty E.
Proof.
move => H ; split ; rewrite /Glb_Rbar /Lub_Rbar ; [ case : (ex_lub_Rbar (fun x : R => x = 0 \/ E x)) => s0 Hs0 ; case : (ex_glb_Rbar (fun x : R => x = 0 \/ E x)) => i0 Hi0 /= | case : (ex_lub_Rbar (fun x : R => x = 1 \/ E x)) => s1 Hs1 ; case : (ex_glb_Rbar (fun x : R => x = 1 \/ E x)) => i1 Hi1 /=].
have : (i0 = Finite 0) ; last move => -> ; apply: Rbar_le_antisym.
apply Hi0 ; by left.
apply Hi0 => y ; case => H0.
rewrite H0 ; by right.
contradict H0 ; apply H.
apply Hs0 => y ; case => H0.
rewrite H0 ; by right.
contradict H0 ; apply H.
apply Hs0 ; by left.
have : (i1 = Finite 1) ; last move => -> ; apply: Rbar_le_antisym.
apply Hi1 ; by left.
apply Hi1 => y ; case => H1.
rewrite H1 ; by right.
contradict H1 ; apply H.
apply Hs1 => y ; case => H1.
rewrite H1 ; by right.
contradict H1 ; apply H.
apply Hs1 ; by left.

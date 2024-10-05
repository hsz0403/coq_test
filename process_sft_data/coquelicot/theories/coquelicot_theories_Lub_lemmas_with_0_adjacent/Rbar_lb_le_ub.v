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

Lemma Rbar_lb_le_ub (E : Rbar -> Prop) (l1 l2 : Rbar) : (exists x, E x) -> Rbar_is_lower_bound E l1 -> Rbar_is_upper_bound E l2 -> Rbar_le l1 l2.
Proof.
intros (x, Hex) Hl Hu ; apply Rbar_le_trans with (y := x) ; [apply Hl | apply Hu] ; auto.

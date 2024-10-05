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

Lemma Empty_correct_1 (E : R -> Prop) : Empty E -> forall x, ~ E x.
Proof.
case => E0 E1 x Ex.
rewrite /Lub_Rbar /Glb_Rbar in E0 ; case : (ex_lub_Rbar (fun x : R => x = 0 \/ E x)) E0 => /= s0 Hs0 ; case : (ex_glb_Rbar (fun x : R => x = 0 \/ E x)) => i0 Hi0 /= E0.
have : (x = 0) ; last move => {s0 Hs0 i0 Hi0 E0}.
apply Rle_antisym.
apply (Rbar_le_trans x s0 0).
apply Hs0 ; by right.
rewrite E0 ; apply Hi0 ; by left.
apply (Rbar_le_trans 0 s0 x).
apply Hs0 ; by left.
rewrite E0 ; apply Hi0 ; by right.
rewrite /Lub_Rbar /Glb_Rbar in E1 ; case : (ex_lub_Rbar (fun x : R => x = 1 \/ E x)) E1 => /= s1 Hs1 ; case : (ex_glb_Rbar (fun x : R => x = 1 \/ E x)) => i1 Hi1 /= E1.
have : (x = 1) ; last move => {s1 Hs1 i1 Hi1 E1}.
apply Rle_antisym.
apply (Rbar_le_trans x s1 1).
apply Hs1 ; by right.
rewrite E1 ; apply Hi1 ; by left.
apply (Rbar_le_trans 1 s1 x).
apply Hs1 ; by left.
rewrite E1 ; apply Hi1 ; by right.
move => -> ; apply R1_neq_R0.

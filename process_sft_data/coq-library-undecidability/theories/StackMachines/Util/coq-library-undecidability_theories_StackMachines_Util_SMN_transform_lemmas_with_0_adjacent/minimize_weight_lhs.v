Require Import Relation_Operators Operators_Properties List Lia PeanoNat.
Import ListNotations.
Require Import Undecidability.StackMachines.SMN.
From Undecidability.StackMachines.Util Require Import Facts List_facts SMN_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.
Local Definition rt_rtn1 := @clos_rt_rtn1_iff Config.
Local Definition app_norm := (@app_assoc', @app_nil_l, @app_nil_r).
Local Arguments rt_trans {A R x y z}.
Module AddFreshLoop.
Section Reduction.
Variables (M : SMN) (L R L' R': list Symbol) (X Y: State).
Variable confluent_M : confluent M.
Arguments confluent_M {X Y1 Y2}.
Variable length_preserving_M : length_preserving M.
Variable XY_neq : X <> Y.
Variable Y_fresh : Forall (fun '((_, _, x), (_, _, y)) => x <> Y /\ y <> Y) M.
Variable lp_XY : length (L++R) = length (L'++R') /\ 1 <= length (L++R).
Definition M' : SMN := [((L, R, X), (L', R', Y)); ((L', R', Y), (L, R, X))] ++ M.
Definition get_state (c: Config) := match c with (_, _, x) => x end.
Definition valid_state (x: State) := x <> Y.
End Reduction.
End AddFreshLoop.
Module DerivableRule.
Section Reduction.
Variables (M : SMN) (L R L' R': list Symbol) (X Y: State).
Variable derivable : reachable M (L, R, X) (L', R', Y).
Variable non_nil : 1 <= length (L ++ R).
Definition M' : SMN := [((L, R, X), (L', R', Y))] ++ M.
End Reduction.
End DerivableRule.
Module DerivableRule'.
Section Reduction.
Variables (M : SMN) (R R': list Symbol) (A: Symbol) (X Y: State).
Variable confluent_M : confluent M.
Variable length_preserving_M : length_preserving M.
Variable derivable : reachable M ([A], R, X) ([A], R', Y).
Variable non_nil : 1 <= length R.
Variable XY_neq : X <> Y.
Variable unique_step_l : forall l r y, step M (l, r, X) y -> l = [A] ++ skipn 1 l.
Variable unique_step_l' : forall l' r' y, step M y (l', r', X) -> l' = [A] ++ skipn 1 l'.
Definition M' : SMN := [(([], R, X), ([], R', Y))] ++ M.
End Reduction.
End DerivableRule'.
Module Reordering.
Section Reduction.
Variables (M1 M2 : SMN) (L R L' R': list Symbol) (X Y: State).
Definition M : SMN := M1 ++ (((L, R, X), (L', R', Y)) :: M2).
Definition M' : SMN := [((L, R, X), (L', R', Y))] ++ M1 ++ M2.
End Reduction.
End Reordering.
Module Transform.
Definition basic (op: Instruction) : bool := match op with | (([], [a], _), ([b], [], _)) => true | (([a], [], _), ([], [b], _)) => true | _ => false end.
Definition weight_Instruction (op: Instruction) : nat := if basic op then 0 else match op with | ((l, r, _), (l', _, _)) => 1 + length (l ++ l' ++ l ++ r) end.
Definition weight (M: SMN) : nat := fold_right (fun op w => w + weight_Instruction op) 0 M.
Fixpoint fresh_State (M: SMN) : State := match M with | [] => 1 | ((_, _, x), (_, _, y)) :: M => 1 + x + y + fresh_State M end.
End Transform.
Inductive basic : Instruction -> Prop := | basic_r a b x y : basic (([], [a], x), ([b], [], y)) | basic_l a b x y : basic (([a], [], x), ([], [b], y)).

Lemma minimize_weight_lhs {M: SMN} {a l r l' r' x y} : In (a :: l, r, x, (l', r', y)) M -> weight_Instruction (a :: l, r, x, (l', r', y)) <> 0 -> confluent M -> length_preserving M -> { M' : SMN | weight M' < weight M /\ (confluent M' /\ length_preserving M' /\ ((exists NM, bounded M NM) <-> (exists NM', bounded M' NM'))) }.
Proof.
move=> HM Hop confluent_M lp_M.
pose z := fresh_State M.
pose M1 := AddFreshLoop.M' M [a] [] [] [a] x z.
pose M2 := DerivableRule.M' M1 l (a::r) l' r' z y.
have : In (a :: l, r, x, (l', r', y)) M2.
{
rewrite /M2 /M1 /AddFreshLoop.M' /DerivableRule.M' ?in_app_iff.
move: HM.
clear.
by firstorder done.
}
move /in_split_informative => /(_ ltac:(by do 5 (decide equality))) => [[[M21 M22] HM2]].
pose M3 := Reordering.M' M21 M22 (a :: l) r l' r' x y.
pose M4 := DerivableRule.M' (M21 ++ M22) (a::l) r l' r' x y.
have ? : x <> z by (move: HM => /fresh_StateP; subst z; lia).
have ? : y <> z by (move: HM => /fresh_StateP; subst z; lia).
have ? : reachable M1 (l, a :: r, z) (l', r', y).
{
apply: AddFreshLoop.step_fresh_rI; first by (move=> /=; lia).
apply: rt_step.
move: HM => /transition => /(_ [] []).
by rewrite ?app_norm.
}
have ? : reachable (M21 ++ M22) (a :: l, r, x) (l', r', y).
{
apply: (rt_trans (y := (l, a :: r, z))); apply: rt_step; (apply: (@DerivableRule.step_neq _ (a :: l) r l' r' x y); first by [left | right]); apply /Reordering.simulation_step; rewrite /Reordering.M -HM2 /M2.
-
apply: (stepI l r [a] [] [] [a] x z); [done | done | clear; by firstorder done ].
-
apply: (stepI [] [] l (a :: r) l' r' z y); [by rewrite ?app_norm | by rewrite ?app_norm | clear; by firstorder done ].
}
exists (M21 ++ M22).
constructor; [| constructor; [| constructor]].
-
suff: weight M2 < weight M + (weight_Instruction (a :: l, r, x, (l', r', y))).
{
rewrite HM2 weight_split.
move: (weight_Instruction _) (weight _).
by lia.
}
move: Hop.
rewrite /M2 /DerivableRule.M' /= /weight_Instruction.
case: (basic (a :: l, r, x, (l', r', y))); first by lia.
move=> _.
case: (basic (l, a :: r, z, (l', r', y))).
{
rewrite /= ?app_length.
by lia.
}
rewrite /= ?app_length /= ?app_length.
by lia.
-
apply /DerivableRule.confluence; first by eassumption.
apply /Reordering.confluence.
rewrite /Reordering.M -HM2.
apply /DerivableRule.confluence; first by eassumption.
apply: AddFreshLoop.confluent_M'; [done | done | by apply: fresh_StateP' | by move=> /=; lia ].
-
apply /DerivableRule.length_preservation; [by eassumption | rewrite app_length /=; lia | ].
apply /Reordering.length_preservation.
rewrite /Reordering.M -HM2.
apply /DerivableRule.length_preservation; [by eassumption | rewrite app_length /=; lia | ].
apply: AddFreshLoop.length_preserving_M'; [done | done | by apply: fresh_StateP' | by move=> /=; lia ].
-
rewrite (DerivableRule.boundedness (M21 ++ M22)); last by eassumption.
rewrite -(Reordering.boundedness M21 M22).
rewrite /Reordering.M -HM2.
rewrite -(DerivableRule.boundedness); last by eassumption.
rewrite -(AddFreshLoop.boundedness); [done | done | by apply: fresh_StateP' | by move=> /=; lia ].

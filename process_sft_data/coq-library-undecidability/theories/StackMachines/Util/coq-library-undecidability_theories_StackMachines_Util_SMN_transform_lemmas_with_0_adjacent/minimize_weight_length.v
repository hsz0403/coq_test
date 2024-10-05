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

Lemma minimize_weight_length {M: SMN} {a r b r' x y} : In (([], a :: r, x), ([], b :: r', y)) M -> weight_Instruction (([], a :: r, x), ([], b :: r', y)) <> 0 -> 1 <= length r -> confluent M -> length_preserving M -> { M' : SMN | weight M' < weight M /\ (confluent M' /\ length_preserving M' /\ ((exists NM, bounded M NM) <-> (exists NM', bounded M' NM'))) }.
Proof.
move=> HM Hop Hr confluent_M lp_M.
pose z1 := fresh_State M.
pose M1 := AddFreshLoop.M' M [] [a] [a] [] x z1.
pose z2 := fresh_State M1.
pose M2 := AddFreshLoop.M' M1 [] [b] [a] [] y z2.
pose M3 := DerivableRule'.M' M2 r r' z1 z2.
have : In ([], a :: r, x, ([], b :: r', y)) M3.
{
rewrite /M3 /M2 /M1 /AddFreshLoop.M' /DerivableRule'.M' ?in_app_iff.
move: HM.
clear.
by firstorder done.
}
move /in_split_informative => /(_ ltac:(by do 5 (decide equality))) => [[[M31 M32] HM3]].
pose M4 := Reordering.M' M31 M32 [] (a::r) [] (b::r') x y.
pose M5 := DerivableRule.M' (M31 ++ M32) [] (a::r) [] (b::r') x y.
have ? : x <> z1 by (move: HM => /fresh_StateP; subst z1; lia).
have ? : y <> z1 by (move: HM => /fresh_StateP; subst z1; lia).
have [? ?] : x <> z2 /\ y <> z2.
{
have /fresh_StateP : In ([], a :: r, x, ([], b :: r', y)) M1.
{
rewrite /M1 /AddFreshLoop.M' ?in_app_iff.
by right.
}
unfold z2; lia.
}
have ? : z1 <> z2.
{
have /fresh_StateP : In ([], [a], x, ([a], [], z1)) M1.
{
rewrite /M1 /AddFreshLoop.M' ?in_app_iff.
left.
by left.
}
unfold z2; lia.
}
have ? : reachable M2 ([a], r, z1) ([a], r', z2).
{
apply: AddFreshLoop.step_fresh_lI; first by (move=> /=; lia).
apply: AddFreshLoop.step_fresh_rI; first by (move=> /=; lia).
apply: rt_step.
move: HM => /transition => /(_ [] []).
by rewrite ?app_norm.
}
have ? : reachable (M31 ++ M32) ([], a::r, x) ([], b :: r', y).
{
apply: (rt_trans (y := ([a], r, z1))); [| apply: (rt_trans (y := ([a], r', z2)))]; apply: rt_step; (apply: (@DerivableRule.step_neq _ [] (a :: r) [] (b :: r') x y); first by [left | right]); apply /Reordering.simulation_step; rewrite /Reordering.M -HM3 /M3.
-
apply: (stepI [] r [] [a] [a] [] x z1); [done | done | clear; by firstorder done].
-
apply: (stepI [a] [] [] r [] r' z1 z2); [by rewrite ?app_norm | by rewrite ?app_norm | clear; by firstorder done].
-
apply: (stepI [] r' [a] [] [] [b] z2 y); [done | done | clear; by firstorder done].
}
have ? : forall l'' r'' z , step M2 (l'', r'', z1) z -> l'' = [a] ++ skipn 1 l''.
{
move=> l'' r'' z.
move HZ1: (l'', r'', z1) => Z1 HZ1z.
case: HZ1z HZ1.
move=> >.
rewrite /M2 /AddFreshLoop.M' /M1 /AddFreshLoop.M' ?in_app_iff.
case.
{
case; [by congruence | case; [by congruence | done]].
}
case.
-
case; first by congruence.
case; last done.
move=> + [] *.
move=> [] *.
by subst.
-
move /fresh_StateP=> ? [] *.
subst z1.
by lia.
}
have ? : forall l'' r'' z , step M2 z (l'', r'', z1) -> l'' = [a] ++ skipn 1 l''.
{
move=> l'' r'' z.
move HZ1: (l'', r'', z1) => Z1 HZ1z.
case: HZ1z HZ1.
move=> >.
rewrite /M2 /AddFreshLoop.M' /M1 /AddFreshLoop.M' ?in_app_iff.
case.
{
case; [by congruence | case; [by congruence | done]].
}
case; [case|].
-
move=> + [] * => [[]] *.
by subst.
-
case; [by congruence | done].
-
move /fresh_StateP=> ? [] *.
subst z1.
by lia.
}
exists (M31 ++ M32).
constructor; [| constructor; [| constructor]].
-
suff: weight M3 < weight M + (weight_Instruction ([], (a::r), x, ([], (b::r'), y))).
{
rewrite HM3 weight_split.
move: (weight_Instruction _) (weight _).
by lia.
}
move: Hop.
rewrite /M3 /DerivableRule.M' /= /weight_Instruction.
case: (basic ([], a :: r, x, ([], b :: r', y))); first by lia.
move=> _.
case: (basic ([], r, z1, ([], r', z2))).
{
rewrite /= ?app_length.
by lia.
}
rewrite /= ?app_length /= ?app_length.
by lia.
-
apply /DerivableRule.confluence; first by eassumption.
apply /Reordering.confluence.
rewrite /Reordering.M -HM3.
apply /DerivableRule'.confluent_M'; [| by eassumption | done | done | done ].
apply: AddFreshLoop.confluent_M'; [ | done | by apply: fresh_StateP' | by move=> /=; lia ].
apply: AddFreshLoop.confluent_M'; [ done | done | by apply: fresh_StateP' | by move=> /=; lia ].
-
apply /DerivableRule.length_preservation; [by eassumption | move=> /=; by lia | ].
apply /Reordering.length_preservation.
rewrite /Reordering.M -HM3.
apply /DerivableRule'.length_preserving_M'; [| by eassumption | done | done | done | done ].
apply: AddFreshLoop.length_preserving_M'; [ | done | by apply: fresh_StateP' | by move=> /=; lia ].
apply: AddFreshLoop.length_preserving_M'; [ done | done | by apply: fresh_StateP' | by move=> /=; lia ].
-
rewrite (DerivableRule.boundedness (M31 ++ M32)); last by eassumption.
rewrite -(Reordering.boundedness M31 M32).
rewrite /Reordering.M -HM3.
rewrite -(DerivableRule'.boundedness); [ | by eassumption | done | done | done | done ].
rewrite -(AddFreshLoop.boundedness); [ | done | by apply: fresh_StateP' | by move=> /=; lia ].
rewrite -(AddFreshLoop.boundedness); [ done | done | by apply: fresh_StateP' | by move=> /=; lia ].

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

Lemma confluent_M' : confluent M'.
Proof using unique_step_l' unique_step_l derivable XY_neq confluent_M.
move=> ? ? ? /rt_rt1n + /rt_rt1n.
case.
{
move=> /rt_rt1n ?.
eexists.
constructor; first by eassumption.
by apply: rt_refl.
}
move=> ? ? Hxy1 /rt_rt1n Hy1z1 Hxy2.
case: Hxy2 Hxy1.
{
move=> ?.
eexists.
constructor; first by apply: rt_refl.
apply: rt_trans; last by eassumption.
by apply: rt_step.
}
move=> ? ? Hxy2 /rt_rt1n Hy2z2 Hxy1.
move: Hy1z1 Hy2z2 => /simulation => /(_ _ Hxy1) Hy1z1 /simulation => /(_ _ Hxy2) Hy2z2.
case: Hxy1 Hxy2 Hy1z1 Hy2z2 => v1 w1 >.
rewrite /M' in_app_iff -/M'.
case.
-
case; last done.
move=> [] <- <- <- <- <- <- /=.
move Hx: (v1, R ++ w1, X) => x Hxy2.
case: Hxy2 Hx => v2 w2 >.
rewrite /M' in_app_iff -/M'.
case.
{
case; last done.
move=> [] <- <- <- <- <- <- [] <- /app_inv_head <- /=.
move=> /confluent_M => H /H => [[? [? ?]]].
eexists.
constructor; apply: inverse_simulation; by eassumption.
}
move /transition => /(_ v2 w2) + H.
rewrite -H.
move=> Hxy2.
move: Hxy2 (Hxy2) => /unique_step_l ->.
move=> /(@rt_step Config) /(@rt_trans Config) => {}H + /H.
have /reachable_stack_app := derivable.
move=> /(_ (skipn 1 v1) w1) /(@rt_trans Config) => {}H /H.
move=> /confluent_M => {}H /H [? [? ?]].
eexists.
constructor; apply: inverse_simulation; by eassumption.
-
move /transition => /(_ v1 w1) Hxy2.
move Hx: (c in step M' c _) => ? Hxy1.
case: Hxy1 Hx Hxy2.
move=> v2 w2 >.
rewrite /M' in_app_iff -/M'.
case.
{
case; last done.
move=> [] <- <- <- <- <- <- /= ->.
move=> Hxy1.
move: Hxy1 (Hxy1) => /unique_step_l ->.
move=> /(@rt_step Config) /(@rt_trans Config) => {}H /H Hxz1.
have /reachable_stack_app := derivable.
move=> /(_ (skipn 1 v2) w2) /(@rt_trans Config) => {}H /H.
move: Hxz1=> /confluent_M {}H /H [? [? ?]].
eexists.
constructor; apply: inverse_simulation; by eassumption.
}
move /transition => /(_ v2 w2) + ->.
move=> /(@rt_step Config) /(@rt_trans Config) => {}H + + /H.
move=> /(@rt_step Config) /(@rt_trans Config) => {}H /H.
move=> /confluent_M => {}H /H [? [? ?]].
eexists.
constructor; apply: inverse_simulation; by eassumption.

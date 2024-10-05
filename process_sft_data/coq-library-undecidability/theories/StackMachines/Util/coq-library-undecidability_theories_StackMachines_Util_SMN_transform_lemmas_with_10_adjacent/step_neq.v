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

Lemma bounded_M' NM : bounded M NM -> bounded M' (NM * (1 + length M') * (1 + length M') * 4).
Proof using lp_XY Y_fresh XY_neq.
move=> bounded_M.
move=> x.
have [Lx [HLx H2Lx]] := next_n_configs M' 1 [x].
have [L2x [HL2x H2L2x]] := concat_reachable Lx bounded_M.
have [L3x [HL3x H2L3x]] := next_n_configs M' 1 L2x.
exists L3x.
constructor.
-
move=> ? /synchronize => [[z1]] [z2] [/HLx] /(_ ltac:(by left)).
by move /HL2x => H [+ /H /HL3x {}H] => /H.
-
suff : length L2x <= NM * (1 + length M') * 2 by move: H2L3x => /=; clear; nia.
move: H2Lx H2L2x => /=.
clear.
Admitted.

Lemma bounded_M NM' : bounded M' NM' -> bounded M NM'.
Proof.
move=> bounded_M' x.
have [Lx [HLx ?]] := bounded_M' x.
exists Lx.
constructor; last done.
Admitted.

Theorem boundedness : (exists NM, bounded M NM) <-> (exists NM', bounded M' NM').
Proof using lp_XY Y_fresh XY_neq.
Admitted.

Lemma length_preserving_M' : length_preserving M'.
Proof using length_preserving_M lp_XY Y_fresh XY_neq.
move=> >.
rewrite /M' in_app_iff.
move=> [[|[|]]|].
-
move=> [] *.
by subst.
-
move: lp_XY => [? ?] [] *.
subst.
constructor; [done | by lia].
-
done.
-
Admitted.

Lemma step_fresh_rI l r l' r' y: reachable M (L ++ l, R ++ r, X) (l', r', y) -> reachable M' (L' ++ l, R' ++ r, Y) (l', r', y).
Proof using lp_XY.
move=> ?.
apply: rt_trans; first last.
-
apply: reachable_incl; last by eassumption.
move=> ? ?.
by firstorder done.
-
apply: rt_step.
apply: transition.
Admitted.

Lemma step_fresh_lI l r l' r' x: reachable M (l, r, x) (L ++ l', R ++ r', X) -> reachable M' (l, r, x) (L' ++ l', R' ++ r', Y) .
Proof using lp_XY.
move=> ?.
apply: rt_trans.
-
apply: reachable_incl; last by eassumption.
move=> ? ?.
by firstorder done.
-
apply: rt_step.
apply: transition.
Admitted.

Lemma simulation {x y} : reachable M' x y <-> reachable M x y.
Proof using derivable.
clear non_nil.
constructor; last by (apply: reachable_incl; apply /incl_appr).
elim.
-
move=> ? ?.
case=> >.
rewrite /M' in_app_iff.
case.
*
case; last done.
move=> [] *.
subst.
by apply: reachable_stack_app.
*
move=> ?.
apply: rt_step.
by apply: transition.
-
move=> *.
by apply: rt_refl.
-
move=> *.
Admitted.

Lemma confluence : confluent M' <-> confluent M.
Proof using derivable.
constructor.
-
move=> HM' ? ? ? /simulation H1 /simulation H2.
have [z [? ?]] := HM' _ _ _ H1 H2.
exists z.
constructor; by apply /simulation.
-
move=> HM ? ? ? /simulation H1 /simulation H2.
have [z [? ?]] := HM _ _ _ H1 H2.
exists z.
Admitted.

Theorem boundedness : (exists NM, bounded M NM) <-> (exists NM', bounded M' NM').
Proof using derivable.
constructor.
-
move=> [NM] HM.
exists NM => x.
have [Lx [HLx ?]]:= HM x.
exists Lx.
constructor; last done.
by move=> ? /simulation /HLx.
-
move=> [NM'] HM'.
exists NM' => x.
have [Lx [HLx ?]]:= HM' x.
exists Lx.
constructor; last done.
Admitted.

Lemma length_preservation : length_preserving M' <-> length_preserving M.
Proof using non_nil derivable.
constructor; first by (apply: length_preserving_incl; right).
move=> HM >.
rewrite /M' in_app_iff.
case; last by move /HM.
case; last done.
move=> [] *.
subst.
move: (derivable) => /(length_preservingP HM).
case; last done.
move=> [] *.
Admitted.

Lemma unique_step_M'l' {l' r' y} : step M' y (l', r', X) -> l' = [A] ++ skipn 1 l'.
Proof using unique_step_l' unique_step_l derivable XY_neq.
move Hx: (l', r', X) => x Hyx.
case: Hyx Hx.
move=> v w >.
rewrite /M' in_app_iff.
case; first by (case; [by congruence | done]).
move /transition => /(_ v w) + [] *.
subst.
Admitted.

Lemma simulation {x y z} : step M' x y -> reachable M' y z -> reachable M y z.
Proof using unique_step_l' unique_step_l derivable XY_neq.
move=> Hxy.
move /rt_rtn1.
elim; first by apply: rt_refl.
move=> y' {}z Hy'z.
case: Hy'z.
move=> v w >.
rewrite /M' in_app_iff.
case; first last.
{
move /transition => *.
apply: rt_trans; first by eassumption.
by apply: rt_step.
}
case; last done.
move=> [] <- <- <- <- <- <-.
rewrite -/M'.
clear y'.
move Hy': ([] ++ v, R ++ w, X) => y' Hyy'.
case: Hyy' Hy' Hxy.
{
move=> <- /= /unique_step_M'l' -> _.
by apply: reachable_stack_app.
}
move=> {}y' {}z + + ?.
subst z.
move=> /= /unique_step_M'l' -> *.
apply: rt_trans; first by eassumption.
Admitted.

Lemma inverse_simulation {x y} : reachable M x y -> reachable M' x y.
Proof.
apply: reachable_incl.
Admitted.

Lemma bounded_M' NM : bounded M NM -> bounded M' (1 + NM * length M').
Proof using unique_step_l' unique_step_l derivable XY_neq non_nil.
move=> bounded_M x.
have [ys [Hys H'ys]] := next_configs M' x.
have [L [HL H'L]] := concat_reachable ys bounded_M.
exists ([x] ++ L).
constructor; first last.
{
move: H'ys H'L.
rewrite app_length /=.
by nia.
}
move=> ? /rt_rt1n Hxz.
rewrite in_app_iff.
case: Hxz Hys; first by (move=> *; left; left).
move=> ? ? Hxy + Hys.
move: Hxy (Hxy) => /Hys ? /simulation Hyz /rt_rt1n ?.
right.
Admitted.

Lemma bounded_M NM' : bounded M' NM' -> bounded M NM'.
Proof.
move=> bounded_M' x.
have [L [HL ?]] := bounded_M' x.
exists L.
constructor; last done.
Admitted.

Theorem boundedness : (exists NM, bounded M NM) <-> (exists NM', bounded M' NM').
Proof using unique_step_l' unique_step_l derivable XY_neq non_nil.
Admitted.

Lemma length_preserving_M' : length_preserving M'.
Proof using unique_step_l' unique_step_l derivable XY_neq non_nil length_preserving_M.
move=> >.
rewrite /M' in_app_iff.
case; last by move /length_preserving_M.
case; last done.
move=> [] *.
subst.
move=> /=.
constructor; last done.
have /length_preservingP := derivable.
move /(_ length_preserving_M).
case; first by congruence.
rewrite ?app_length /=.
Admitted.

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
Admitted.

Lemma simulation {x y} : reachable M' x y <-> reachable M x y.
Proof.
Admitted.

Lemma confluence : confluent M' <-> confluent M.
Proof.
Admitted.

Lemma step_neq {l r x l' r' y} : X <> x \/ Y <> y -> step M' (l, r, x) (l', r', y) -> step M (l, r, x) (l', r', y).
Proof.
move Hx': (l, r, x) => x'.
move Hy': (l', r', y) => y' H Hx'y'.
case: Hx'y' Hx' Hy' H => > /= [].
-
move=> ? ? ? [?|?]; by congruence.
-
move /transition => + ? ? ?.
by apply.

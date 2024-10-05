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

Lemma step_neq {l r x l' r' y} : X <> x \/ Y <> y -> step M' (l, r, x) (l', r', y) -> step M (l, r, x) (l', r', y).
Proof.
move Hx': (l, r, x) => x'.
move Hy': (l', r', y) => y' H Hx'y'.
case: Hx'y' Hx' Hy' H => > /= [].
-
move=> ? ? ? [?|?]; by congruence.
-
move /transition => + ? ? ?.
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

Lemma boundedness' {n} : bounded M' n <-> bounded M n.
Proof.
constructor.
-
move=> HM' x.
have [Lx [HLx ?]]:= HM' x.
exists Lx.
constructor; last done.
by move=> ? /simulation /HLx.
-
move=> HM x.
have [Lx [HLx ?]]:= HM x.
exists Lx.
constructor; last done.
Admitted.

Theorem boundedness : (exists NM, bounded M NM) <-> (exists NM', bounded M' NM').
Proof.
Admitted.

Lemma length_preservation : length_preserving M' <-> length_preserving M.
Proof.
rewrite /M' /M.
Admitted.

Lemma simulation_step {x y} : step M' x y <-> step M x y.
Proof.
Admitted.

Lemma fresh_StateP {M: SMN} {l r x l' r' y} : In ((l, r, x), (l', r', y)) M -> x < fresh_State M /\ y < fresh_State M.
Proof.
elim: M; first done.
move=> [[[l1 r1] x1] [[l2 r2] x2]] M IH /= [|].
-
move=> [] *.
subst.
by lia.
-
move /IH.
Admitted.

Lemma weight_split op M1 M2 : weight (M1 ++ op :: M2) = weight_Instruction op + weight (M1 ++ M2).
Proof.
elim: M1.
-
move=> /=.
by lia.
-
move=> op1 M1 /= ->.
Admitted.

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
Admitted.

Lemma minimize_weight_rhs {M: SMN} {a r l' r' x y} : In (([], r, x), (a :: l', r', y)) M -> weight_Instruction (([], r, x), (a :: l', r', y)) <> 0 -> confluent M -> length_preserving M -> { M' : SMN | weight M' < weight M /\ (confluent M' /\ length_preserving M' /\ ((exists NM, bounded M NM) <-> (exists NM', bounded M' NM'))) }.
Proof.
move=> HM Hop confluent_M lp_M.
pose z := fresh_State M.
pose M1 := AddFreshLoop.M' M [a] [] [] [a] y z.
pose M2 := DerivableRule.M' M1 [] r l' (a::r') x z.
have : In ([], r, x, (a :: l', r', y)) M2.
{
rewrite /M2 /M1 /AddFreshLoop.M' /DerivableRule.M' ?in_app_iff.
move: HM.
clear.
by firstorder done.
}
move /in_split_informative => /(_ ltac:(by do 5 (decide equality))) => [[[M21 M22] HM2]].
pose M3 := Reordering.M' M21 M22 [] r (a::l') r' x y.
pose M4 := DerivableRule.M' (M21 ++ M22) [] r (a::l') r' x y.
have ? : x <> z by (move: HM => /fresh_StateP; subst z; lia).
have ? : y <> z by (move: HM => /fresh_StateP; subst z; lia).
have ? : reachable M1 ([], r, x) (l', a::r', z).
{
apply: AddFreshLoop.step_fresh_lI; first by (move=> /=; lia).
apply: rt_step.
move: HM => /transition => /(_ [] []).
by rewrite ?app_norm.
}
have ? : reachable (M21 ++ M22) ([], r, x) (a :: l', r', y).
{
apply: (rt_trans (y := (l', a :: r', z))); apply: rt_step; (apply: (@DerivableRule.step_neq _ [] r (a::l') r' x y); first by [left | right]); apply /Reordering.simulation_step; rewrite /Reordering.M -HM2 /M2.
-
apply: (stepI [] [] [] r l' (a :: r') x z); [by rewrite ?app_norm | by rewrite ?app_norm | clear; by firstorder done ].
-
apply: (stepI l' r' [] [a] [a] [] z y); [done | done | clear; by firstorder done].
}
exists (M21 ++ M22).
constructor; [| constructor; [| constructor]].
-
suff: weight M2 < weight M + (weight_Instruction ([], r, x, (a::l', r', y))).
{
rewrite HM2 weight_split.
move: (weight_Instruction _) (weight _).
by lia.
}
move: Hop.
rewrite /M2 /DerivableRule.M' /= /weight_Instruction.
case: (basic ([], r, x, (a :: l', r', y))); first by lia.
move=> _.
case: (basic ([], r, x, (l', a :: r', z))).
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
apply /DerivableRule.length_preservation; [by eassumption | move: HM => /lp_M; by lia | ].
apply /Reordering.length_preservation.
rewrite /Reordering.M -HM2.
apply /DerivableRule.length_preservation; [by eassumption | move: HM => /lp_M; by lia | ].
apply: AddFreshLoop.length_preserving_M'; [done | done | by apply: fresh_StateP' | by move=> /=; lia ].
-
rewrite (DerivableRule.boundedness (M21 ++ M22)); last by eassumption.
rewrite -(Reordering.boundedness M21 M22).
rewrite /Reordering.M -HM2.
rewrite -(DerivableRule.boundedness); last by eassumption.
Admitted.

Lemma minimize_weight_short {M: SMN} {a b x y} : In (([], [a], x), ([], [b], y)) M -> confluent M -> length_preserving M -> { M' : SMN | weight M' < weight M /\ (confluent M' /\ length_preserving M' /\ ((exists NM, bounded M NM) <-> (exists NM', bounded M' NM'))) }.
Proof.
move=> HM confluent_M lp_M.
pose z := fresh_State M.
pose M1 := AddFreshLoop.M' M [] [a] [a] [] x z.
pose M2 := DerivableRule.M' M1 [a] [] [] [b] z y.
have : In ([], [a], x, ([], [b], y)) M2.
{
rewrite /M2 /M1 /AddFreshLoop.M' /DerivableRule.M' ?in_app_iff.
move: HM.
clear.
by firstorder done.
}
move /in_split_informative => /(_ ltac:(by do 5 (decide equality))) => [[[M21 M22] HM2]].
pose M3 := Reordering.M' M21 M22 [] [a] [] [b] x y.
pose M4 := DerivableRule.M' (M21 ++ M22) [] [a] [] [b] x y.
have ? : x <> z by (move: HM => /fresh_StateP; subst z; lia).
have ? : y <> z by (move: HM => /fresh_StateP; subst z; lia).
have ? : reachable M1 ([a], [], z) ([], [b], y).
{
apply: AddFreshLoop.step_fresh_rI; first by (move=> /=; lia).
apply: rt_step.
move: HM => /transition => /(_ [] []).
by rewrite ?app_norm.
}
have ? : reachable (M21 ++ M22) ([], [a], x) ([], [b], y).
{
apply: (rt_trans (y := ([a], [], z))); apply: rt_step; (apply: (@DerivableRule.step_neq _ [] [a] [] [b] x y); first by [left | right]); apply /Reordering.simulation_step; rewrite /Reordering.M -HM2 /M2.
-
apply: (stepI [] [] [] [a] [a] [] x z); [done | done | clear; by firstorder done].
-
apply: (stepI [] [] [a] [] [] [b] z y); [done | done | clear; by firstorder done].
}
exists (M21 ++ M22).
constructor; [| constructor; [| constructor]].
-
suff: weight M2 < weight M + (weight_Instruction ([], [a], x, ([], [b], y))).
{
rewrite HM2 weight_split.
move: (weight_Instruction _) (weight _).
by lia.
}
rewrite /weight_Instruction /basic.
rewrite /M2 /DerivableRule.M' /= /weight_Instruction /=.
by lia.
-
apply /DerivableRule.confluence; first by eassumption.
apply /Reordering.confluence.
rewrite /Reordering.M -HM2.
apply /DerivableRule.confluence; first by eassumption.
apply: AddFreshLoop.confluent_M'; [done | done | by apply: fresh_StateP' | by move=> /=; lia ].
-
apply /DerivableRule.length_preservation; [by eassumption | move=> /=; by lia | ].
apply /Reordering.length_preservation.
rewrite /Reordering.M -HM2.
apply /DerivableRule.length_preservation; [by eassumption | move=> /=; by lia | ].
apply: AddFreshLoop.length_preserving_M'; [done | done | by apply: fresh_StateP' | by move=> /=; lia ].
-
rewrite (DerivableRule.boundedness (M21 ++ M22)); last by eassumption.
rewrite -(Reordering.boundedness M21 M22).
rewrite /Reordering.M -HM2.
rewrite -(DerivableRule.boundedness); last by eassumption.
Admitted.

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
Admitted.

Lemma overweight_Instruction {M} : weight M <> 0 -> { op | In op M /\ weight_Instruction op <> 0 }.
Proof.
elim: M; first done.
move=> op M IH /=.
have [-> ? |] : { weight M = 0 } + { weight M <> 0 } by decide equality.
-
exists op.
constructor; [by left | done].
-
move /IH => [op' [? ?]] _.
exists op'.
Admitted.

Theorem minimize_weight (M: SMN) : confluent M -> length_preserving M -> { M' : SMN | weight M' = 0 /\ (confluent M' /\ length_preserving M' /\ ((exists NM, bounded M NM) <-> (exists NM', bounded M' NM'))) }.
Proof.
elim /(measure_rect weight): M => M IH confluent_M lp_M.
have [? |] : {weight M = 0} + {weight M <> 0} by decide equality.
{
exists M.
by firstorder done.
}
move /overweight_Instruction => [[[[l r] x] [[l' r'] y]] []].
move: l => [|a l]; first last.
{
move /minimize_weight_lhs => H /H => /(_ confluent_M lp_M) => [[M' [? [? [? ?]]]]].
case: (IH M'); [ done | done | done |].
move=> M'' [? [? [? HM'']]].
exists M''.
constructor; [done | constructor; [ done | constructor; [done | by rewrite -HM'']]].
}
move: l' => [|a l']; first last.
{
move /minimize_weight_rhs => H /H => /(_ confluent_M lp_M) => [[M' [? [? [? ?]]]]].
case: (IH M'); [ done | done | done |].
move=> M'' [? [? [? HM'']]].
exists M''.
constructor; [done | constructor; [ done | constructor; [done | by rewrite -HM'']]].
}
move: r => [|a r]; first by (move /lp_M => /=; lia).
move: r' => [|b r']; first by (move /lp_M => /=; lia).
move: r => [|a' r].
-
move: r' => [|? ?]; last by (move /lp_M => /=; lia).
move=> + _ => /minimize_weight_short => /(_ confluent_M lp_M) => [[M' [? [? [? ?]]]]].
case: (IH M'); [ done | done | done |].
move=> M'' [? [? [? HM'']]].
exists M''.
constructor; [done | constructor; [ done | constructor; [done | by rewrite -HM'']]].
-
have : 1 <= length (a' :: r) by (move=> /=; lia).
move: (a' :: r) => {}r.
move /minimize_weight_length => H /H => {}H /H => /(_ confluent_M lp_M) => [[M' [? [? [? ?]]]]].
case: (IH M'); [ done | done | done |].
move=> M'' [? [? [? HM'']]].
exists M''.
Admitted.

Theorem construct_basic_SMN (M: SMN) : confluent M -> length_preserving M -> { M' : SMN | Forall basic M' /\ (confluent M' /\ ((exists NM, bounded M NM) <-> (exists NM', bounded M' NM'))) }.
Proof.
move /Transform.minimize_weight => H /H => [[M']] [HM'] [? [_ ?]].
exists M'.
constructor; last by constructor.
apply /Forall_forall => op /(@in_split Instruction) => [[?]] [? ?].
subst M'.
move: HM'.
rewrite Transform.weight_split => ?.
have : Transform.weight_Instruction op = 0 by lia.
clear.
rewrite /Transform.weight_Instruction.
case Hop: (Transform.basic op); last by move: op Hop => [[[l r] ?] [[l' r'] ?]].
move: op Hop => [[[l r] ?] [[l' r'] ?]] /=.
Admitted.

Lemma fresh_StateP' (M: SMN) : Forall (fun '((_, _, x), (_, _, y)) => x <> fresh_State M /\ y <> fresh_State M) M.
Proof.
rewrite Forall_forall.
move=> [[[l1 r1] x1] [[l2 r2] x2]] /fresh_StateP.
by lia.

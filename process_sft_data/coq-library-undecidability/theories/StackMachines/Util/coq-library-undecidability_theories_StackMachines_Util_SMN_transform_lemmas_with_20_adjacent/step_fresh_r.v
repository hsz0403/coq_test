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

Lemma step_fresh_l {l r x} : step M' (l, r, Y) x -> x = (L ++ skipn (length L') l, R ++ skipn (length R') r, X).
Proof using lp_XY Y_fresh XY_neq.
move Hy: (l, r, Y) => y Hyx.
case: Hyx Hy => > + [] *.
subst.
rewrite /M' in_app_iff.
move=> [[|[|]]|].
-
move=> [] *.
by congruence.
-
move=> [] *.
subst.
by rewrite ?skipn_app ?Nat.sub_diag ?skipn_all.
-
done.
-
have := Y_fresh.
rewrite Forall_forall.
Admitted.

Lemma simulation {n x y} : reachable_n M' n x y -> valid_state (get_state x) -> valid_state (get_state y) -> reachable_n M n x y.
Proof using lp_XY Y_fresh XY_neq.
elim: n x y; first by (move=> > /reachable_0E -> *; apply: rn_refl).
move=> n IH x y /reachable_SnE [|]; first by (move=> -> *; apply: rn_refl).
move=> [z1].
have : {get_state z1 = Y} + {get_state z1 <> Y} by decide equality.
case; first last.
{
move=> Hz1 [Hxz1] /IH {}IH Hx ?.
apply: rn_step; last by apply: IH.
move: Hxz1 Hx Hz1 => /step_app.
case; last done.
case=> > [|[|]]; move=> [] /= *; by congruence.
}
move: n IH => [|n] IH; first by (move=> ? [_ /reachable_0E ?]; congruence).
move=> + [+ /reachable_SnE H].
case: H; first by congruence.
move=> [z2] [+].
move: z1 => [[l1 r1] z1] /= + + ?.
subst z1.
move: x z2 => [[l r] x] [[l2 r2] z2].
move=> /step_fresh_l [] ? ? ? + /step_fresh_r [] => *.
subst.
apply: (reachable_n_monotone (m := S n)); first by lia.
apply: IH; [|done|done].
apply: reachable_n_monotone; last by eassumption.
Admitted.

Lemma simulation' {x y} : reachable M' x y -> valid_state (get_state x) -> valid_state (get_state y) -> reachable M x y.
Proof using lp_XY Y_fresh XY_neq.
Admitted.

Lemma inverse_simulation {n x y} : reachable_n M n x y -> reachable_n M' n x y.
Proof.
move=> ?.
apply: reachable_n_incl; last by eassumption.
Admitted.

Lemma inverse_simulation' {x y} : reachable M x y -> reachable M' x y.
Proof.
move=> ?.
apply: reachable_incl; last by eassumption.
Admitted.

Lemma continue {x y} : reachable M' x y -> valid_state (get_state x) -> exists z, reachable M' y z /\ valid_state (get_state z).
Proof using lp_XY Y_fresh XY_neq.
have : {get_state y = Y} + {get_state y <> Y} by decide equality.
case; first last.
{
move=> *.
eexists.
by constructor; first by apply: rt_refl.
}
move=> Hy.
move /rt_rtn1 => Hxy.
case: Hxy Hy; first by congruence.
move=> ? ? /step_app.
case; first last.
{
case=> >.
have := Y_fresh.
rewrite Forall_forall => H /H /= [].
by congruence.
}
case=> v w > /= [|[|]]; [| by congruence | done].
move=> [] <- <- <- <- <- <- _ _ _.
exists (L ++ v, R ++ w, X).
constructor; last done.
apply: rt_step.
apply: transition.
right.
Admitted.

Lemma synchronize_step {x y} : step M' x y -> exists z, reachable_n M' 1 x z /\ reachable_n M' 1 z y /\ valid_state (get_state z).
Proof using lp_XY Y_fresh XY_neq.
move=> /copy => [[[]]] >.
rewrite /M' in_app_iff -/M'.
move=> [[|[|]]|].
-
move=> [] <- <- <- <- <- <- ?.
eexists.
constructor; first by apply: rn_refl.
by constructor; first by (apply: rn_step; [by eassumption | by apply: rn_refl]).
-
move=> [] <- <- <- <- <- <- ?.
eexists.
constructor; first by (apply: rn_step; [by eassumption | by apply: rn_refl]).
by constructor; first by apply: rn_refl.
-
done.
-
have := Y_fresh.
rewrite Forall_forall => H /H [? ?] ?.
eexists.
constructor; first by apply: rn_refl.
Admitted.

Lemma synchronize {x y} : reachable M' x y -> exists z1 z2, reachable_n M' 1 x z1 /\ reachable_n M' 1 z2 y /\ reachable M z1 z2.
Proof using lp_XY Y_fresh XY_neq.
move /rt_rt1n.
case.
{
exists x, x.
constructor; first by apply: rn_refl.
constructor; first by apply: rn_refl.
by apply: rt_refl.
}
move=> ? ? + /rt_rt1n /rt_rtn1 Hz1y.
case: Hz1y.
{
move /synchronize_step => [z] [? [? ?]].
exists z, z.
constructor; first done.
constructor; first done.
by apply: rt_refl.
}
move=> ? ? /synchronize_step => [[z2]] [/reachable_n_to_reachable ? [? ?]].
move=> /rt_rtn1 ? /synchronize_step => [[z1]] [? [/reachable_n_to_reachable ? ?]].
exists z1, z2.
constructor; first done.
constructor; first done.
apply: simulation'; [| done | done].
apply: rt_trans; first by eassumption.
Admitted.

Lemma confluent_valid_M' {x y1 y2} : valid_state (get_state x) -> reachable M' x y1 -> reachable M' x y2 -> exists z : Config, reachable M' y1 z /\ reachable M' y2 z.
Proof using confluent_M lp_XY Y_fresh XY_neq.
move=> Hx Hxy1 Hxy2.
move: (Hxy1) => /continue => /(_ Hx).
move=> [z1 [Hy1z1 ?]].
move: (Hxy2) => /continue => /(_ Hx).
move=> [z2 [Hy2z2 ?]].
have Hxz1 : reachable M x z1.
{
apply: simulation'; [| done | done].
by apply: rt_trans; last by eassumption.
}
have Hxz2 : reachable M x z2.
{
apply: simulation'; [| done | done].
by apply: rt_trans; last by eassumption.
}
have [? [? ?]]:= confluent_M Hxz1 Hxz2.
eexists.
Admitted.

Theorem confluent_M' : confluent M'.
Proof using confluent_M lp_XY Y_fresh XY_neq.
move=> x y1 y2.
have : {get_state x = Y} + {get_state x <> Y} by decide equality.
case; first last.
{
move=> *.
apply: confluent_valid_M'; by eassumption.
}
move=> Hx /rt_rt1n Hxy1.
case: Hxy1 Hx.
{
move=> *.
eexists.
constructor; first by eassumption.
by apply: rt_refl.
}
move=> {}y1 y1' + + + /rt_rt1n Hxy2.
case: Hxy2.
-
move=> ? /rt_rt1n ? ?.
eexists.
constructor; first by apply: rt_refl.
apply: rt_trans; last by eassumption.
by apply: rt_step.
-
move=> {}y2 y2'.
move: x y1 y2 => [[l r] x] [[l1 r1] y1] [[l2 r2] y2].
move=> + + + + /= Hx.
subst x.
move=> /step_fresh_l [] ? ? ? + /step_fresh_l [] ? ? ?.
subst.
move=> /rt_rt1n H1 /rt_rt1n H2.
Admitted.

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

Lemma step_fresh_r {l r x} : step M' x (l, r, Y) -> x = (L ++ skipn (length L') l, R ++ skipn (length R') r, X).
Proof using lp_XY Y_fresh XY_neq.
move Hy: (l, r, Y) => y Hyx.
case: Hyx Hy => > + [] *.
subst.
rewrite /M' in_app_iff.
move=> [[|[|]]|].
-
move=> [] *.
subst.
by rewrite ?skipn_app ?Nat.sub_diag ?skipn_all.
-
move=> [] *.
by congruence.
-
done.
-
have := Y_fresh.
rewrite Forall_forall.
by move=> H /H [].

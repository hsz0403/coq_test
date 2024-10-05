Require Import PeanoNat Lia Relation_Operators Operators_Properties List.
Import ListNotations.
Require Import ssreflect ssrfun ssrbool.
Require Import Undecidability.StackMachines.SSM.
From Undecidability.StackMachines.Util Require Import Facts.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Definition width : config -> nat := fun '(A, B, _) => length A + length B.
Section CSSM.
Context {M : ssm}.
Variable confluent_M : confluent M.
Arguments confluent_M {X Y1 Y2}.
Definition equiv (X Y: config) := exists (Z: config), reachable M X Z /\ reachable M Y Z.
Fixpoint enum_stacks (n: nat) : list stack := if n is S n then (map (cons true) (enum_stacks n)) ++ (map (cons false) (enum_stacks n)) else [[]].
Fixpoint enum_states (M': ssm) : list state := match M' with | [] => [] | (x, y, _, _, _) :: M' => x :: y :: enum_states M' end.
Definition get_state : config -> state := fun '(_, _, x) => x.
Definition enum_configs (lA lB: nat) : list config := list_prod (list_prod (enum_stacks lA) (enum_stacks lB)) (enum_states M).
Definition space (X: config) : list config := X :: flat_map (fun i => enum_configs i (width X - i)) (seq 0 (width X + 1)).
Definition get_left : config -> stack := fun '(A, _, _) => A.
Definition get_right : config -> stack := fun '(_, B, _) => B.
Inductive reachable_n : nat -> config -> config -> Prop := | rn_refl n X : reachable_n n X X | rn_step n X Y Z: reachable_n n X Y -> step M Y Z -> reachable_n (1+n) X Z.
Definition narrow (X: config) := exists (x: state) (A: stack), equiv X (A, [], x).
Definition bounded' (n: nat) : Prop := forall (c: config) (x y: state) (A B: stack), reachable M (A, [], x) c -> reachable M ([], B, y) c -> length B <= n.
End CSSM.

Lemma extend_bounded' {n: nat} {X: config} : bounded' n -> narrow X -> length (get_right X) <= n.
Proof using confluent_M.
move: X => [[A B] x] Hn.
elim /(measure_ind (@length symbol)) : A => A IH.
case: (stack_eq_dec A []).
{
move=> -> [y [A']] [Z [+ ?]].
move /Hn.
apply.
by eassumption.
}
move /exists_last => [A' [a HA]].
subst A.
rename A' into A.
move=> [y [A']] [Z [Hx]].
case: (stack_eq_dec A' []).
{
move=> ->.
move: Hx => /reachable_width + /reachable_width => <- /=.
by lia.
}
move /exists_last => [A'' [a' HA']].
subst A'.
rename A'' into A'.
move: Z Hx => [[A'' B''] z] /copy [/remove_rendundant_suffixL].
case.
{
move=> [x' [B']] /copy [/reachable_width] /= HB Hx1 Hx2 Hy.
have [Y [HY1 HY2]] := (confluent_M Hx1 Hx2).
move: Hy HY2 HY1 => /(@rt_trans config).
move=> H /H{H}.
move /Hn => H /H{H}.
by lia.
}
move=> /= [A''' [? Hx]].
subst A''.
rename A''' into A''.
move=> _ /copy [/remove_rendundant_suffixL].
case.
{
move=> [x' [B']].
move=> /copy [/reachable_width] /=.
rewrite app_length => /= ?.
move /Hn.
move /(_ _ _ ltac:(apply: rt_refl)) => ?.
move: Hx => /reachable_width + /reachable_width => /=.
rewrite ?app_length => /=.
by lia.
}
move=> [A'''].
move=> [/(@app_inj_tail symbol) [? ?]].
subst.
move=> ? _.
apply: (IH A).
-
rewrite app_length /length.
by lia.
-
do 3 eexists.
constructor; by eassumption.

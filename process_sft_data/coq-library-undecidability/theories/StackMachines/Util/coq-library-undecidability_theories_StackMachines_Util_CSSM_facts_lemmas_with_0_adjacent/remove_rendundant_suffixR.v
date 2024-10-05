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

Lemma remove_rendundant_suffixR {x: state} {A B: stack} {b: symbol} {Y: config} : reachable M (A, B++[b], x) Y -> (exists (x': state) (A': stack), reachable M (A, B++[b], x) (A', [], x')) \/ (exists (D: stack), get_right Y = D ++ [b] /\ reachable M (A, B, x) (get_left Y, D, get_state Y)).
Proof.
move HX: (A, B ++ [b], x) => X H.
elim: H x A B b HX.
-
move=> ? ?.
case.
+
move=> > ? >.
case=> -> <- ->.
right.
eexists.
constructor.
*
rewrite app_comm_cons.
by reflexivity.
*
apply: rt_step.
by apply: step_l.
+
move=> x y a b A.
case.
*
move=> ? > _.
left.
exists y, (a::A).
apply: rt_step.
by apply: step_r.
*
move=> b' B ? >.
have [B'' [b'' ->]] := (@exists_last _ (b' :: B) ltac:(done)).
case=> ?.
rewrite app_comm_cons.
move /(@app_inj_tail symbol).
case=> ? ? ?.
subst.
right.
exists B''.
constructor; first done.
apply: rt_step.
by apply: step_r.
-
move=> > <-.
right.
eexists.
constructor; first by reflexivity.
by apply: rt_refl.
-
move=> {}X {}[[A' B'] x'] Z.
move=> _ IH1 _ IH2 x A B b ?.
subst.
case: (IH1 x A B b ltac:(done)).
{
move=> ?.
by left.
}
move=> /= [D' [? Hxx']].
subst.
case: (IH2 x' A' D' b ltac:(done)).
+
move=> [x'' [A'' ?]].
left.
exists x'', A''.
apply: rt_trans; last by eassumption.
have -> : (A = A ++ []) by rewrite app_nil_r.
have -> : (A' = A' ++ []) by rewrite app_nil_r.
by apply: reachable_app.
+
move=> [D'' [? ?]].
right.
exists D''.
constructor; first done.
apply: rt_trans; by eassumption.

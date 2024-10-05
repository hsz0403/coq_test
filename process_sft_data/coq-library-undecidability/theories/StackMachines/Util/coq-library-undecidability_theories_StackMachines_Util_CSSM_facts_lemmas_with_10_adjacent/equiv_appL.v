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

Lemma stack_eq_dec (A B: stack) : {A = B} + {A <> B}.
Proof.
Admitted.

Lemma reachable_app {x x': state} {A B A' B' C D: stack} : reachable M (A, B, x) (A', B', x') -> reachable M (A++C, B++D, x) (A'++C, B'++D, x').
Proof.
move HX: (A, B, x) => X.
move HX': (A', B', x') => X'.
move=> H.
elim: H C D x x' A B A' B' HX HX'; clear.
-
move=> X X'.
case; clear.
+
move=> > H >.
case=> -> -> ->.
case=> -> -> ->.
apply: rt_step.
by apply: step_l.
+
move=> > H >.
case=> -> -> ->.
case=> -> -> ->.
apply: rt_step.
by apply: step_r.
-
move=> > <-.
case=> -> -> ->.
by apply: rt_refl.
-
move=> X [[A' B'] x'] Z ? IHXY ? IHYZ *.
Admitted.

Lemma equiv_refl {X: config} : equiv X X.
Proof.
exists X.
Admitted.

Lemma equiv_sym {X Y: config} : equiv X Y <-> equiv Y X.
Proof.
Admitted.

Lemma equiv_trans {X Y Z: config} : equiv X Y -> equiv Y Z -> equiv X Z.
Proof using confluent_M.
move=> [Z0 [? HYZ0]] [Z1 [HYZ1 ?]].
have [Z2 [? ?]] := (confluent_M HYZ0 HYZ1).
exists Z2.
Admitted.

Lemma equiv_app {x x': state} {A B A' B' C D: stack} : equiv (A, B, x) (A', B', x') -> equiv (A++C, B++D, x) (A'++C, B'++D, x').
Proof.
move=> [[[A'' B''] x''] [? ?]].
exists (A''++C, B''++D, x'').
Admitted.

Corollary equiv_appR {x x': state} {A B A' B': stack} {b: bool} : equiv (A, B, x) (A', B', x') -> equiv (A, B ++ [b], x) (A', B' ++ [b], x').
Proof.
move /(equiv_app (C := []) (D := [b])).
Admitted.

Lemma enum_stacksP {A: stack} : In A (enum_stacks (length A)).
Proof.
elim: A => /=; first by left.
move=> a A IH.
rewrite in_app_iff ? in_map_iff.
Admitted.

Lemma enum_statesP {x y: state} {a b: symbol} {d: dir} : In (x, y, a, b, d) M -> In x (enum_states M) /\ In y (enum_states M).
Proof.
elim: M x y a b d=> /=; clear; first done.
move=> i M IH >.
case.
-
move=> ->.
constructor; [by left | by right; left].
-
move /IH=> [? ?].
move: i=> [[[[? ?] ?] ?] ?].
Admitted.

Lemma enum_states_step {X Y: config} : step M X Y -> In (get_state X) (enum_states M) /\ In (get_state Y) (enum_states M).
Proof.
Admitted.

Lemma enum_states_reachable {X Y: config} : reachable M X Y -> X = Y \/ (In (get_state X) (enum_states M) /\ In (get_state Y) (enum_states M)).
Proof.
elim.
-
move=> ? ? /enum_states_step ?.
by right.
-
move=> ?.
by left.
-
move=> > _ + _.
case.
+
move=> ->.
case; [move=> ->; by left | move=> ?; by right].
+
move=> [? ?].
Admitted.

Lemma enum_configsP (x: state) (A B: stack) : In x (enum_states M) -> In (A, B, x) (enum_configs (length A) (length B)).
Proof.
move=> Hx.
rewrite /enum_configs ? in_prod_iff.
have ? := enum_stacksP.
Admitted.

Lemma reachable_width {X Y: config} : reachable M X Y -> width X = width Y.
Proof.
elim; clear.
-
move=> X Y.
case=> *; rewrite /width /length; by lia.
-
done.
-
move=> *.
Admitted.

Lemma spaceP {X Y: config} : In (get_state X) (enum_states M) -> width X = width Y -> In X (space Y).
Proof.
rewrite /space.
case: X => [[A B] x].
move=> HX <-.
right.
apply /in_flat_map.
exists (length A).
constructor=> /=.
{
apply /in_seq.
by lia.
}
have -> : (length A + length B - length A = length B) by lia.
Admitted.

Lemma spaceP0 {X Y: config} : reachable M X Y -> In Y (space X).
Proof.
move=> /copy [/enum_states_reachable + /reachable_width].
case.
-
move=> <- _.
by left.
-
move=> [_ /spaceP] + ?.
Admitted.

Lemma space_equivP {X Y: config} : equiv X Y -> In Y (space X).
Proof.
move=> [Z] /copy [[/reachable_width + /reachable_width]] => <- /spaceP HY.
move=> [/enum_states_reachable + /enum_states_reachable].
case.
-
move=> <-.
case.
+
move=> <-.
by left.
+
move=> [? ?].
by apply: HY.
-
move=> [? ?].
case.
+
move=> ?.
subst Z.
by apply: HY.
+
move=> [? ?].
Admitted.

Lemma step_dec (X Y: config) : decidable (step M X Y).
Proof.
case: (Exists_dec (fun '(x, y, a, b, d) => (get_state X, get_state Y, if d then get_left X else b :: get_left X, if d then b :: get_right X else get_right X) = (x, y, if d then a :: get_left Y else get_left Y, if d then get_right Y else a :: get_right Y)) M).
-
move=> [[[[x y] a] b] d].
do 4 (decide equality).
-
move=> H.
left.
move: H.
rewrite Exists_exists.
move=> [[[[[x y] a] b] d]].
case: d.
+
move=> [?].
move: X Y => [[A ?] ?] [[? B] ?] /=.
case: A; case: B=> //=.
move=> >.
case=> *.
subst.
by apply: step_l.
+
move=> [?].
move: X Y => [[? B] ?] [[A ?] ?] /=.
case: A; case: B=> //=.
move=> >.
case=> *.
subst.
by apply: step_r.
-
move=> H.
right.
move=> HXY.
apply: H.
rewrite Exists_exists.
case: HXY.
+
move=> x y a b A B H.
exists (x, y, a, b, true) => /=.
by constructor.
+
move=> x y a b A B H.
exists (x, y, b, a, false) => /=.
Admitted.

Corollary equiv_appL {x x': state} {A B A' B': stack} {a: bool} : equiv (A, B, x) (A', B', x') -> equiv (A++[a], B, x) (A'++[a], B', x').
Proof.
move /(equiv_app (C := [a]) (D := [])).
by rewrite ? app_nil_r.

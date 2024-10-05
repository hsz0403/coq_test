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

Lemma reachable_dec (X Y: config) : decidable (reachable M X Y).
Proof.
have := reachable_n_dec (length (space X)) X Y.
case=> HXY; [left | right].
-
apply: reachable_n_to_reachable.
by eassumption.
-
move /reachable_to_reachable_n => [n H'XY].
apply: HXY.
apply: reachable_n_bounded; last by eassumption.
move=> *.
apply: spaceP0.
apply: reachable_n_to_reachable.
Admitted.

Lemma equiv_dec (X Y: config) : decidable (equiv X Y).
Proof.
case: (Exists_dec (fun Z => reachable M X Z /\ reachable M Y Z) (space X)).
-
move=> Z.
case: (reachable_dec X Z) => ?; case: (reachable_dec Y Z) => ?; by firstorder done.
-
move=> + /ltac:(left).
rewrite Exists_exists.
move=> [Z [? ?]].
eexists.
by eassumption.
-
move=> + /ltac:(right) => + [Z [? ?]].
apply.
rewrite Exists_exists.
exists Z.
Admitted.

Lemma narrow_dec (X: config) : decidable (narrow X).
Proof.
case: (Exists_dec (fun Y => get_right Y = [] /\ equiv X Y) (space X)).
-
move=> [[A + ] y].
case; first last.
{
move=> >.
right.
by move=> [+].
}
case: (equiv_dec X (A, [], y)).
+
move=> ?.
by left.
+
move=> ?.
right.
by move=> [_].
-
move=> + /ltac:(left).
rewrite Exists_exists.
move=> [[[A B] y] [_]] /= [->] ?.
by exists y, A.
-
move=> + /ltac:(right) => + [y [A HX]].
rewrite Exists_exists.
apply.
exists (A, [], y).
constructor; last done.
Admitted.

Lemma narrow_appL {x: state} {A B: stack} {a: bool} : narrow (A, B, x) -> narrow (A ++ [a], B, x).
Proof.
move=> [y [A']].
move /(equiv_app (C := [a]) (D := [])).
rewrite ? app_nil_r => ?.
do 2 eexists.
Admitted.

Lemma remove_rendundant_suffixL {x: state} {A B: stack} {a: symbol} {Y: config}: reachable M (A++[a], B, x) Y -> (exists (x': state) (B': stack), reachable M (A++[a], B, x) ([], B', x')) \/ (exists (C: stack), get_left Y = C ++ [a] /\ reachable M (A, B, x) (C, get_right Y, get_state Y)).
Proof.
move HX: (A ++ [a], B, x) => X H.
elim: H x A B a HX.
-
move=> ? ?.
case.
+
move=> x y a b.
case.
*
move=> B ? > _.
left.
exists y, (b::B).
apply: rt_step.
by apply: step_l.
*
move=> a' A B ? >.
have [A'' [a'' ->]] := (@exists_last _ (a' :: A) ltac:(done)).
case.
rewrite app_comm_cons.
move /(@app_inj_tail symbol).
case=> ? ? ? ?.
subst.
right.
exists A''.
constructor; first done.
apply: rt_step.
by apply: step_l.
+
move=> > ? >.
case=> <- -> ->.
right.
eexists.
constructor.
*
rewrite app_comm_cons.
by reflexivity.
*
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
move=> _ IH1 _ IH2 x A B a ?.
subst.
case: (IH1 x A B a ltac:(done)).
{
move=> ?.
by left.
}
move=> /= [C' [? Hxx']].
subst.
case: (IH2 x' C' B' a ltac:(done)).
+
move=> [x'' [B'' ?]].
left.
exists x'', B''.
apply: rt_trans; last by eassumption.
have -> : (B = B ++ []) by rewrite app_nil_r.
have -> : (B' = B' ++ []) by rewrite app_nil_r.
by apply: reachable_app.
+
move=> [C'' [? ?]].
right.
exists C''.
constructor; first done.
Admitted.

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
Admitted.

Lemma bounded_stack_difference {n: nat} {x y: state} {A B C D: stack} : bounded M n -> reachable M (A, B, x) (C, D, y) -> length B <= length D + n /\ length D <= length B + n.
Proof.
move /(_ (A, B, x)) => [L [HL1 HL2]].
move /reachable_to_reachable_n => [m].
move /(reachable_n_bounded (L := L)).
apply: unnest.
{
move=> *.
apply: HL1.
apply: reachable_n_to_reachable.
by eassumption.
}
move /reachable_n_monotone => /(_ n ltac:(lia)).
clear m HL1 HL2 L.
elim: n x y A B C D.
{
move=> > /reachable_0E [] *.
subst.
by lia.
}
move=> n IH x y A B C D /reachable_SnE.
case.
{
move=> [] *.
subst.
by lia.
}
move=> [[[C' D'] z]] [/IH] {}IH.
move HZ: (C', D', z) => Z.
move HY: (C, D, y) => Y HZY.
case: HZY HZ HY.
-
move=> > _ [] ? ? ? [] ? ? ?.
subst.
move: IH.
rewrite /length -?/(length _).
by lia.
-
move=> > _ [] ? ? ? [] ? ? ?.
subst.
move: IH.
rewrite /length -?/(length _).
Admitted.

Lemma length_flat_map_le {X: Type} {f g: nat -> list X} {l1 l2: nat} : l1 <= l2 -> (forall i, length (f i) <= length (g i)) -> length (flat_map f (seq 0 l1)) <= length (flat_map g (seq 0 l2)).
Proof.
move: (X in (seq X)) => i.
move=> + Hfg.
elim: l1 l2 i.
{
move=> /= *.
by lia.
}
move=> l1 IH l2 i ?.
have -> : (l2 = S (l2 - 1)) by lia.
move=> /=.
rewrite ? app_length.
have := (IH (l2 - 1) (S i) ltac:(lia)).
have := (Hfg i).
Admitted.

Lemma length_enum_stacks {l: nat} : length (enum_stacks l) = Nat.pow 2 l.
Proof.
elim: l; first done.
move=> l /=.
rewrite app_length ? map_length.
move=> ->.
Admitted.

Lemma length_enum_configs {lA lB} : length (enum_configs lA lB) = length (enum_stacks lA) * length (enum_stacks lB) * length (enum_states M).
Proof.
Admitted.

Theorem reachable_suffixes (X: config) : (exists A x y B, reachable M X (A, [], x) /\ reachable M X ([], B, y)) \/ (exists AX a, get_left X = AX ++ [a] /\ forall Y, reachable M X Y -> exists AY, get_left Y = AY ++ [a] /\ reachable M (AX, get_right X, get_state X) (AY, get_right Y, get_state Y)) \/ (exists BX b, get_right X = BX ++ [b] /\ forall Y, reachable M X Y -> exists BY, get_right Y = BY ++ [b] /\ reachable M (get_left X, BX, get_state X) (get_left Y, BY, get_state Y)).
Proof.
case: (Exists_dec (fun Y => get_right Y = [] /\ reachable M X Y) (space X)).
{
move=> [[A +] x].
case; first last.
-
move=> >.
right.
by move => [? ?].
-
case: (reachable_dec X (A, [], x)); first last.
+
move=> >.
right.
by move => [? ?].
+
move=> ?.
by left.
}
1: case: (Exists_dec (fun Y => get_left Y = [] /\ reachable M X Y) (space X)).
{
move=> [[+ B] x].
case; first last.
-
move=> >.
right.
by move => [? ?].
-
case: (reachable_dec X ([], B, x)); first last.
+
move=> >.
right.
by move => [? ?].
+
move=> ?.
by left.
}
all: rewrite ?Exists_exists.
-
move=> [[[A1 B1] x1]] + [[[A2 B2] x2]] => /= [[_ [? ?]]] [_ [? ?]].
subst.
left.
do 4 eexists.
constructor; by eassumption.
-
move=> HX _.
right.
left.
case: (stack_eq_dec (get_left X) []).
{
move=> ?.
exfalso.
apply: HX.
exists X.
constructor; first by left.
constructor; first done.
apply: rt_refl.
}
move /exists_last => [A [a HAa]].
exists A, a.
constructor; first done.
move=> Y.
move: X HX HAa => [[AX BX] xX] HX /= HAa.
subst.
case /remove_rendundant_suffixL; last done.
move=> [x' [B' ?]].
exfalso.
apply: HX.
exists ([], B', x').
constructor; first by apply: spaceP0.
by constructor.
-
move=> HX.
right.
right.
case: (stack_eq_dec (get_right X) []).
{
move=> ?.
exfalso.
apply: HX.
exists X.
constructor; first by left.
constructor; first done.
apply: rt_refl.
}
move /exists_last => [B [b HBb]].
exists B, b.
constructor; first done.
move=> Y.
move: X HX HBb => [[AX BX] xX] HX /= HBb.
subst.
case /remove_rendundant_suffixR; last done.
move=> [x' [A' ?]].
exfalso.
apply: HX.
exists (A', [], x').
constructor; first by apply: spaceP0.
Admitted.

Lemma bounded_of_bounded' {n: nat}: bounded' n -> exists (m: nat), bounded M m.
Proof using confluent_M.
move=> Hn.
pose W := (repeat false n, repeat false n, 0) : config.
exists (length (space W)).
elim /(measure_ind width).
move=> X IH.
case: (reachable_suffixes X); last case.
-
move=> [?] [?] [?] [?] [+ /copy] => /confluent_M H [/H{H}] [Y].
move=> [/Hn] H /H{H} ? /reachable_width HwX.
move=> /= in HwX.
exists (space X).
constructor.
+
by move=> ? /spaceP0.
+
apply: space_length => /=.
rewrite repeat_length.
by lia.
-
move: X IH => [[A B] x] IH.
move=> [AX] [a] [HA HX].
move=> /= in HA.
subst.
case: (IH (AX, B, x)).
{
move=> /=.
rewrite app_length /length.
by lia.
}
move=> L [HL1 HL2].
exists (map (fun '(A, B, x) => (A ++ [a], B, x)) L).
constructor; last by rewrite map_length.
move=> [[A' y] B'] /HX [AY] /= [->] /HL1 ?.
rewrite in_map_iff.
eexists.
by constructor; last by eassumption.
-
move: X IH => [[A B] x] IH.
move=> [BX] [b] [HB HX].
move=> /= in HB.
subst.
case: (IH (A, BX, x)).
{
move=> /=.
rewrite app_length /length.
by lia.
}
move=> L [HL1 HL2].
exists (map (fun '(A, B, x) => (A, B ++ [b], x)) L).
constructor; last by rewrite map_length.
move=> [[A' y] B'] /HX [BY] /= [->] /HL1 ?.
rewrite in_map_iff.
eexists.
Admitted.

Lemma bounded_to_bounded' {n: nat}: bounded M n -> exists (m: nat), bounded' m.
Proof.
move=> Hn.
exists (n+n).
rewrite /bounded'.
move=> [[A' B'] z] x y A B /(bounded_stack_difference Hn) + /(bounded_stack_difference Hn) => /=.
Admitted.

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
Admitted.

Theorem boundedP : (exists n, bounded M n) <-> (exists m, bounded' m).
Proof using confluent_M.
constructor.
-
move=> [?].
by apply /bounded_to_bounded'.
-
move=> [?].
Admitted.

Lemma narrow_equiv {X Y: config} : equiv X Y -> narrow X -> narrow Y.
Proof using confluent_M.
move=> /equiv_sym HXY [x [A HX]].
exists x, A.
Admitted.

Lemma space_length {X Y: config} : width X <= width Y -> length (space X) <= length (space Y).
Proof.
rewrite /space => /=.
move: (width X) => l1.
move: (width Y) => l2.
clear.
move=> H.
apply: le_n_S.
apply: length_flat_map_le; first by lia.
move=> i.
rewrite ? length_enum_configs ? length_enum_stacks.
have ?: 2 ^ (l1 - i) <= 2 ^ (l2 - i).
{
apply: Nat.pow_le_mono_r; by lia.
}
suff : 2 ^ i * 2 ^ (l1 - i) <= 2 ^ i * 2 ^ (l2 - i) by nia.
by nia.

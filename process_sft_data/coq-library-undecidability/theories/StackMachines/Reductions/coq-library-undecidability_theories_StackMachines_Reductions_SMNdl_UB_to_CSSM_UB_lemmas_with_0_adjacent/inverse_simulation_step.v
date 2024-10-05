Require Import List Lia.
Import ListNotations.
Require Import Relation_Operators Operators_Properties.
Require Import Undecidability.StackMachines.SMN.
Require Undecidability.StackMachines.SSM.
From Undecidability.StackMachines.Util Require Import Nat_facts List_facts SMN_facts.
Require Import Undecidability.StackMachines.Util.SMN_transform.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Section Reduction.
Variable M : SMN.
Variable confluent_M : confluent M.
Variable basic_M : Forall basic M.
Definition encode_Instruction (op: Instruction) : SSM.instruction := match op with | (([], [a], x), ([b], [], y)) => (x, y, a, b, false) | (([a], [], x), ([], [b], y)) => (x, y, a, b, true) | _ => (0, 0, true, true, true) end.
Definition M' : SSM.ssm := map encode_Instruction M.
End Reduction.
End Argument.
Require Import Undecidability.Synthetic.Definitions.
Local Definition SMNdl_to_cssm : { M : SMN | deterministic M /\ length_preserving M } -> SSM.cssm.
Proof.
move=> [M [/deterministic_confluent H1M H2M]].
exists (Argument.M' (sval (construct_basic_SMN M H1M H2M))).
apply: Argument.confluent_M'.
-
exact (fst (snd (svalP (construct_basic_SMN M H1M H2M)))).
-
exact (fst ((svalP (construct_basic_SMN M H1M H2M)))).
Defined.

Lemma inverse_simulation_step {x y} : SSM.step M' x y -> step M x y.
Proof using basic_M.
case=> >.
-
rewrite /M' in_map_iff.
move=> [[[[l r] {}x] [[l' r'] {}y]]] [] + HM.
move: HM (HM) => /basic_instructions.
move H1op: (l, r, x, (l', r', y)) => op H2op.
case: H2op H1op.
+
move=> > /=.
by congruence.
+
move=> > [] /= ? ? ? ? ? ? + [] *.
subst.
move /transition.
by apply.
-
rewrite /M' in_map_iff.
move=> [[[[l r] {}x] [[l' r'] {}y]]] [] + HM.
move: HM (HM) => /basic_instructions.
move H1op: (l, r, x, (l', r', y)) => op H2op.
case: H2op H1op.
+
move=> > [] /= ? ? ? ? ? ? + [] *.
subst.
move /transition.
by apply.
+
move=> > /=.
by congruence.

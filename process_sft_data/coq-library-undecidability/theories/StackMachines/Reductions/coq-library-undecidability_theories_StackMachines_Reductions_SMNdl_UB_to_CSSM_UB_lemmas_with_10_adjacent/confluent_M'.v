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

Lemma basic_instructions : forall op, In op M -> basic op.
Proof using basic_M.
Admitted.

Lemma simulation_step {x y} : step M x y -> SSM.step M' x y.
Proof using basic_M.
case=> v w l r l' r' {}x {}y Hop.
move: Hop (Hop) => /basic_instructions.
move H1op: (l, r, x, (l', r', y)) => op H2op.
case: H2op H1op.
-
move=> > [] *.
subst.
apply: SSM.step_r.
rewrite /M' in_map_iff.
eexists.
by constructor; last by eassumption.
-
move=> > [] *.
subst.
apply: SSM.step_l.
rewrite /M' in_map_iff.
eexists.
Admitted.

Lemma simulation {x y} : reachable M x y -> SSM.reachable M' x y.
Proof using basic_M.
elim.
-
move=> ? ? /simulation_step ?.
by apply: rt_step.
-
move=> *.
by apply: rt_refl.
-
move=> *.
Admitted.

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
Admitted.

Lemma inverse_simulation {x y} : SSM.reachable M' x y -> reachable M x y.
Proof using basic_M.
elim.
-
move=> ? ? /inverse_simulation_step ?.
by apply: rt_step.
-
move=> *.
by apply: rt_refl.
-
move=> *.
Admitted.

Lemma boundedness : (exists NM, bounded M NM) <-> (exists NM', SSM.bounded M' NM').
Proof using basic_M.
constructor.
-
move=> [NM bounded_M].
exists NM.
move=> X.
have [L [HL ?]] := bounded_M X.
exists L.
constructor; last done.
by move=> ? /inverse_simulation /= /HL ?.
-
move=> [NM' bounded_M'].
exists NM'.
move=> X.
have [L [HL ?]] := bounded_M' X.
exists L.
constructor; last done.
Admitted.

Theorem reduction : SMNdl_UB ⪯ SSM.CSSM_UB.
Proof.
exists SMNdl_to_cssm.
move=> [M [H1M H2M]].
constructor.
-
move=> [nMN] /=.
set M1 := (construct_basic_SMN M (deterministic_confluent H1M) H2M).
move=> HM.
have [? [?]] := svalP M1.
move /iffLR => /(_ ltac:(by eexists)) => /Argument.boundedness.
by apply.
-
move /Argument.boundedness.
set M1 := (construct_basic_SMN M (deterministic_confluent H1M) H2M).
have [? [? <-]] := svalP M1.
Admitted.

Lemma confluent_M' : SSM.confluent M'.
Proof using basic_M confluent_M.
move=> ? ? ? /inverse_simulation /= H1 /inverse_simulation /= H2.
have [? []] := confluent_M _ _ _ H1 H2.
move=> /simulation /= ? /simulation /= ?.
eexists.
constructor; by eassumption.

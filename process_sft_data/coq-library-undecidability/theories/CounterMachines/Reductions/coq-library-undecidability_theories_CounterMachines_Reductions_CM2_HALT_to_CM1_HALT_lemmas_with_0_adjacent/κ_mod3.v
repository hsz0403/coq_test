Require Import List PeanoNat Lia.
Import ListNotations.
Require Undecidability.CounterMachines.CM2.
Require Undecidability.CounterMachines.CM1.
Import CM2 (CM2_HALT).
Import CM1 (CM1_HALT).
From Undecidability.CounterMachines.Util Require Import Nat_facts List_facts.
From Undecidability.CounterMachines.Util Require CM1_facts CM2_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Import CM2 (Cm2).
Import CM1 (Cm1).
Section MM2_CM1.
Variable (P: Cm2).
Definition fs (i: nat) : CM1.State := i*6.
Definition encode_instruction : CM2.Instruction * nat -> list CM1.Instruction := fun '(cm2i, i) => let p := fs i in match cm2i with | CM2.inc false => [(fs (1+i), 0)] ++ (* 2/1, goto i+1 *) [(0, 0); (0, 0); (0, 0); (0, 0); (0, 0)] (* filler *) | CM2.inc true => [(1+p, 0); (fs (1+i), 1)] ++ (* 2/1; 3/2, goto i+1 *) [(0, 0); (0, 0); (0, 0); (0, 0)] (* filler *) | CM2.dec false j => [(4+p, 1)] ++ (* 3/2 *) [(2+p, 0); (3+p, 0); (fs (1+i), 3)] ++ (* fail: 2/1; 2/1; 5/4 goto i+1 *) [(5+p, 2); (fs j, 3)] (* success: 4/3; 5/4 goto j *) | CM2.dec true j => [(4+p, 2)] ++ (* 4/3 *) [(2+p, 0); (3+p, 0); (fs (1+i), 3)] ++ (* fail: 2/1; 2/1; 5/4 goto i+1 *) [(fs j, 3)] ++ (* success: 5/4 goto j *) [(0, 0)] (* filler *) end.
Local Arguments encode_instruction : simpl never.
Definition M : list CM1.Instruction := flat_map encode_instruction (combine P (seq 0 (length P))).
Definition κ (a b c: nat) : nat := 2 ^ a * 3 ^ b * 5 ^ c.
Definition encodes_config (x: CM2.Config) (y: CM1.Config) : Prop := CM1.state y = fs (CM2.state x) /\ exists n, CM1.value y = κ (CM2.value1 x) (CM2.value2 x) n.
Local Arguments encodes_config !x !y /.
Arguments nth_error : simpl never.
Arguments Nat.div : simpl never.
Arguments Nat.modulo : simpl never.
Definition κ_norm := (@κ_pos, @κ_21, @κ_32, @κ_43, @κ_54, @κ_mod2, @κ_mod3, @κ_mod4).
End MM2_CM1.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma κ_mod3 {a b c: nat} : κ a b c mod 3 = if b is 0 then (S (locked (κ a b c) mod 3 - 1)) else 0.
Proof.
rewrite /κ -lock.
rewrite [(_ * 5^_) mod 3]Nat.mul_mod; first by lia.
rewrite [(_ * 3^_) mod 3]Nat.mul_mod; first by lia.
move: b => [|b].
{
by case: (pow_2_mod_3 a); case: (pow_5_mod_3 c); move=> -> ->.
}
have -> : 3 ^ S b = 3 * 3 ^ b by move=> /=; lia.
rewrite [(3 * _) mod 3]Nat.mul_mod; first by lia.
by rewrite ?((@Nat.mod_same 3 ltac:(lia)), (@Nat.mod_0_l 3 ltac:(lia)), Nat.mul_0_r).

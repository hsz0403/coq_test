Require Import Relation_Operators Lia PeanoNat List.
Import ListNotations.
Require Undecidability.CounterMachines.CM1.
Module CM := CM1.
Require Undecidability.CounterMachines.Util.CM1_facts.
Module CM_facts := CM1_facts.
Require Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.SMX.
Require Import Undecidability.StackMachines.SMN.
From Undecidability.StackMachines.Util Require Import Facts Nat_facts List_facts Enumerable.
Require Import Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.CM1_to_SMX.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Local Instance Prefix_Enumerable : Enumerable Prefix.
Proof.
apply: (enumarableI (fun x => if x is Try then 0 else if x is Yes then 1 else 2) (fun x => if x is 0 then Try else if x is 1 then Yes else No)).
by case.
Local Instance BasicState_Enumerable : Enumerable BasicState.
Proof.
apply: (enumarableI (fun x => match x with | is_bounded b => (0, to_nat b) | index p n => (1, to_nat (p, n)) | increase p n => (2, to_nat (p, n)) end) (fun x => match x with | (0, n) => is_bounded (of_nat n) | (1, n) => let '(p, n) := of_nat n in index p n | (2, n) => let '(p, n) := of_nat n in increase p n | _ => is_bounded false end)).
case; move=> *; by rewrite ?enumP.
Local Instance State_Enumerable : Enumerable State.
Proof.
apply: (enumarableI (fun x => match x with | basic_state X => (0, to_nat X) | goto n X Y => (1, to_nat (n, X, Y)) end) (fun x => match x with | (0, n) => basic_state (of_nat n) | (1, n) => let '(n, X, Y) := of_nat n in goto n X Y | _ => basic_state (is_bounded false) end)).
case; move=> *; by rewrite ?enumP.
Section Reduction.
Variable MX : SMX.SMX (State := State) (Symbol := Symbol).
Variable deterministic_MX : SMX.deterministic MX.
Variable length_preserving_MX : forall s t X s' t' Y b, In ((s, t, X), (s', t', Y), b) MX -> length (s ++ t) = length (s' ++ t') /\ 1 <= length (s ++ t).
Variable flip_consistent_MX : forall s1 t1 X c b1 s2 t2 c2 b2, In ((s1, t1, X), c, b1) MX -> In ((s2, t2, X), c2, b2) MX -> b1 = b2.
Local Definition SMX_Instruction := SMX.Instruction (State := State) (Symbol := Symbol).
Definition encode_Symbol (a: Symbol) : bool := if a is zero then false else true.
Definition decode_Symbol (a: bool) : Symbol := if a is false then zero else one.
Definition encode_Stack (s: list Symbol) : list bool := map encode_Symbol s.
Definition decode_Stack (s: list bool) : list Symbol := map decode_Symbol s.
Definition encode_Instruction : SMX_Instruction -> list Instruction := fun '((r, s, x), (r', s', y), b) => if b is true then [ ((encode_Stack r, encode_Stack s, to_nat (x, false)), (encode_Stack r', encode_Stack s', to_nat (y, true))); ((encode_Stack s, encode_Stack r, to_nat (x, true)), (encode_Stack s', encode_Stack r', to_nat (y, false))) ] else [ ((encode_Stack r, encode_Stack s, to_nat (x, false)), (encode_Stack r', encode_Stack s', to_nat (y, false))); ((encode_Stack s, encode_Stack r, to_nat (x, true)), (encode_Stack s', encode_Stack r', to_nat (y, true))) ].
Definition MN: SMN := flat_map encode_Instruction MX.
Section Transport.
Variable NMX : nat.
Variable bounded_MX : SMX.bounded MX NMX.
End Transport.
Section Reflection.
Variable NMN : nat.
Variable bounded_MN : bounded MN NMN.
Definition encode_State : State * bool -> nat := to_nat.
Definition decode_State : nat -> State * bool := of_nat.
End Reflection.
End Reduction.
End Argument.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.CounterMachines.CM1.

Lemma encode_Stack_inj {s t: list Symbol} : encode_Stack s = encode_Stack t -> s = t.
Proof.
move /(f_equal decode_Stack).
by rewrite ?decode_encode_Stack.

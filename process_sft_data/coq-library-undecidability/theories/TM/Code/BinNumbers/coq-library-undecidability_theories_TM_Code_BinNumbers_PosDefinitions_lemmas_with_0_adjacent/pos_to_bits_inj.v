From Undecidability.TM Require Import ProgrammingTools.
From Undecidability.TM Require Import EncodeBinNumbers.
From Undecidability.TM Require Export ArithPrelim.
From Coq Require Export BinPos.
Local Open Scope positive_scope.
Definition append_bit (p : positive) (b : bool) := if b then p~1 else p~0.
Notation "p ~~ b" := (append_bit p b) (at level 7, left associativity, format "p '~~' b") : positive_scope.
Definition bitToSigPos (b : bool) : sigPos := if b then sigPos_xI else sigPos_xO.
Definition bitToSigPos' (b : bool) : sigPos^+ := inr (bitToSigPos b).
Fixpoint append_bits (x : positive) (bits : list bool) : positive := match bits with | nil => x | b :: bits' => append_bits (x~~b) bits' end.
Goal encode_pos (append_bits 1234567890 [false;true;true]) = encode_pos 1234567890 ++ map bitToSigPos [false;true;true].
Proof.
reflexivity.
Fixpoint bits_to_pos' (bits : list bool) : positive := match bits with | nil => 1 | b :: bits' => (bits_to_pos' bits') ~~ b end.
Definition bits_to_pos (bits : list bool) := bits_to_pos' (rev bits).
Fixpoint pos_to_bits (p : positive) : list bool := match p with | 1 => [] | p ~ 1 => pos_to_bits p ++ [true] | p ~ 0 => pos_to_bits p ++ [false] end.
Arguments bits_to_pos : simpl never.
Fixpoint pushHSB (p : positive) (b : bool) : positive := match p with | p' ~ 1 => (pushHSB p' b) ~ 1 | p' ~ 0 => (pushHSB p' b) ~ 0 | 1 => 1 ~~ b end.
Fixpoint shift_left (p : positive) (n : nat) := match n with | O => p | S n' => shift_left (p~0) n' end.
Definition removeLSB (p : positive) : positive := match p with | 1 => 1 | p~0 => p | p~1 => p end.
Fixpoint shift_right (p : positive) (n : nat) := match n with | O => p | S n' => shift_right (removeLSB p) n' end.
Fixpoint pos_size (p : positive) : nat := match p with | 1 => 0 | p~1 => S (pos_size p) | p~0 => S (pos_size p) end.

Lemma pos_to_bits_inj : forall (p1 p2 : positive), pos_to_bits p1 = pos_to_bits p2 -> p1 = p2.
Proof.
intros.
apply Encode_positive_injective.
cbn.
rewrite !Encode_positive_eq_pos_to_bits.
f_equal.
f_equal.
auto.

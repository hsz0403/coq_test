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

Lemma Encode_positive_app_xI (p : positive) : encode_pos (p ~ 0) = encode_pos p ++ [sigPos_xO].
Proof.
cbn.
Admitted.

Lemma Encode_positive_app_xO (p : positive) : encode_pos (p ~ 1) = encode_pos p ++ [sigPos_xI].
Proof.
cbn.
Admitted.

Lemma Encode_positive_app_xIO (p : positive) (b : bool) : encode_pos (p ~~ b) = encode_pos p ++ [if b then sigPos_xI else sigPos_xO].
Proof.
destruct b.
apply Encode_positive_app_xO.
Admitted.

Goal encode_pos (append_bits 1234567890 [false;true;true]) = encode_pos 1234567890 ++ map bitToSigPos [false;true;true].
Proof.
Admitted.

Lemma append_bits_bit (b : bool) (p : positive) (bits : list bool) : append_bits p (b :: bits) = append_bits (p~~b) bits.
Proof.
Admitted.

Lemma encode_append_bits (p : positive) (bits : list bool) : encode_pos (append_bits p bits) = encode_pos p ++ map bitToSigPos bits.
Proof.
revert p.
induction bits; intros; cbn in *; auto.
-
now simpl_list.
-
rewrite IHbits.
rewrite Encode_positive_app_xIO.
simpl_list; cbn.
Admitted.

Lemma bits_to_pos'_cons (bit : bool) (bits : list bool) : bits_to_pos' (bit :: bits) = (bits_to_pos' bits) ~~ bit.
Proof.
Admitted.

Lemma bits_to_pos_cons (bit : bool) (bits : list bool) : bits_to_pos (bits ++ [bit]) = (bits_to_pos bits) ~~ bit.
Proof.
unfold bits_to_pos.
simpl_list; cbn.
Admitted.

Lemma encode_bits_to_pos (bits : list bool) : encode_pos (bits_to_pos bits) = sigPos_xH :: map bitToSigPos bits.
Proof.
unfold bits_to_pos.
rewrite encode_bits_to_pos'.
Admitted.

Lemma pos_to_bits_to_pos (p : positive) : bits_to_pos (pos_to_bits p) = p.
Proof.
induction p; cbn; f_equal; eauto.
-
simpl_list; cbn.
f_equal.
eauto.
-
simpl_list; cbn.
f_equal.
Admitted.

Lemma pos_to_bits_app_bit (b : bool) (p : positive) : pos_to_bits (p ~~ b) = pos_to_bits p ++ [b].
Proof.
Admitted.

Lemma bits_to_pos_to_bits' (bits : list bool) : pos_to_bits (bits_to_pos' bits) = rev bits.
Proof.
induction bits; intros; cbn in *.
-
auto.
-
simpl_list; cbn.
rewrite pos_to_bits_app_bit.
f_equal.
Admitted.

Lemma bits_to_pos_to_bits (bits : list bool) : pos_to_bits (bits_to_pos bits) = bits.
Proof.
unfold bits_to_pos.
rewrite bits_to_pos_to_bits'.
Admitted.

Lemma pos_to_bits_append_bits : forall bits p, pos_to_bits (append_bits p bits) = pos_to_bits p ++ bits.
Proof.
induction bits; intros; cbn in *.
-
now simpl_list.
-
Admitted.

Lemma pos_to_bits_append_bits' : forall bits1 bits2, pos_to_bits (append_bits (bits_to_pos bits1) bits2) = bits1 ++ bits2.
Proof.
intros.
rewrite pos_to_bits_append_bits.
Admitted.

Lemma Encode_positive_eq_pos_to_bits (p : positive) : encode_pos p = sigPos_xH :: map bitToSigPos (pos_to_bits p).
Proof.
induction p; cbn; auto.
-
rewrite IHp; simpl_list; cbn; auto.
-
Admitted.

Lemma pos_to_bits_inj : forall (p1 p2 : positive), pos_to_bits p1 = pos_to_bits p2 -> p1 = p2.
Proof.
intros.
apply Encode_positive_injective.
cbn.
rewrite !Encode_positive_eq_pos_to_bits.
f_equal.
f_equal.
Admitted.

Lemma encode_pushHSB (p : positive) (b : bool) : encode_pos (pushHSB p b) = sigPos_xH :: bitToSigPos b :: tl (encode_pos p).
Proof.
induction p; cbn.
-
rewrite IHp.
simpl_list; cbn.
now rewrite tl_app by apply Encode_positive_eq_nil.
-
rewrite IHp.
simpl_list; cbn.
now rewrite tl_app by apply Encode_positive_eq_nil.
-
rewrite Encode_positive_app_xIO.
cbn.
Admitted.

Lemma encode_bits_to_pos' (bits : list bool) : encode_pos (bits_to_pos' bits) = sigPos_xH :: map bitToSigPos (rev bits).
Proof.
induction bits; cbn in *; f_equal; auto.
rewrite Encode_positive_app_xIO.
rewrite IHbits.
cbn.
f_equal.
simpl_list.
cbn.
auto.

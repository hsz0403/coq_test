From smpl Require Import Smpl.
Require Import Omega Lia.
Require Export Psatz Arith.
Require Export RelationClasses Morphisms.
Instance add_le_mono : Proper (le ==> le ==> le) plus.
Proof.
repeat intro.
now apply Nat.add_le_mono.
Instance mult_le_mono : Proper (le ==> le ==> le) mult.
Proof.
repeat intro.
now apply Nat.mul_le_mono.
Instance max_le_mono : Proper (le ==> le ==> le) max.
Proof.
repeat intro.
repeat eapply Nat.max_case_strong;lia.
Instance max'_le_mono : Proper (le ==> le ==> le) Init.Nat.max.
Proof.
repeat intro.
repeat eapply Nat.max_case_strong;lia.
Instance S_le_mono : Proper (le ==> le) S.
Proof.
repeat intro.
lia.

Instance add_le_mono : Proper (le ==> le ==> le) plus.
Proof.
repeat intro.
Admitted.

Instance max_le_mono : Proper (le ==> le ==> le) max.
Proof.
repeat intro.
Admitted.

Instance max'_le_mono : Proper (le ==> le ==> le) Init.Nat.max.
Proof.
repeat intro.
Admitted.

Instance S_le_mono : Proper (le ==> le) S.
Proof.
repeat intro.
Admitted.

Instance mult_le_mono : Proper (le ==> le ==> le) mult.
Proof.
repeat intro.
now apply Nat.mul_le_mono.

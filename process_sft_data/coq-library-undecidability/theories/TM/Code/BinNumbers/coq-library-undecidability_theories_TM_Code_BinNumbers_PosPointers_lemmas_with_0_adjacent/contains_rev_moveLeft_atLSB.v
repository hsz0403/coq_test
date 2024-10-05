From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import BinNumbers.EncodeBinNumbers.
From Undecidability Require Import BinNumbers.PosDefinitions.
Local Open Scope positive_scope.
Definition atBit (t : tape sigPos^+) (lp : positive) (mb : bool) (rs : list bool) := exists (ls : list sigPos^+), t = midtape (map inr (rev (encode lp)) ++ inl START :: ls) (bitToSigPos' mb) (map bitToSigPos' rs ++ [inl STOP]).
Definition atLSB (t : tape sigPos^+) (lp : positive) (mb : bool) := atBit t lp mb nil.
Definition atHSB (t : tape sigPos^+) (p : positive) := exists (ls : list sigPos^+), t = midtape (inl START :: ls) (inr sigPos_xH) (map inr (tl (encode p)) ++ [inl STOP]).
Ltac atBit_ext := once lazymatch goal with | [ H : atBit ?t ?p0 ?b0 ?bits0 |- atBit ?t ?p1 ?b1 ?bits0 ] => apply (atBit_ext H); auto | [ H : atLSB ?t ?p0 ?b0 |- atLSB ?t ?p1 ?b1 ] => apply (atLSB_ext H); auto | [ H : atHSB ?t ?p0 |- atHSB ?t ?p1 ] => apply (atHSB_ext H); auto end.

Lemma contains_rev_moveLeft_atLSB (t : tape sigPos^+) (lp : positive) (mb : bool) : t ≂ (lp ~~ mb) -> atLSB (tape_move t Lmove) lp mb.
Proof.
intros (ls&->); cbn.
hnf.
rewrite Encode_positive_app_xIO.
rewrite <- !map_rev.
destruct mb; cbn.
-
rewrite rev_app_distr; cbn.
eexists.
f_equal.
f_equal.
f_equal.
now rewrite map_id.
-
rewrite rev_app_distr; cbn.
eexists.
f_equal.
f_equal.
f_equal.
now rewrite map_id.

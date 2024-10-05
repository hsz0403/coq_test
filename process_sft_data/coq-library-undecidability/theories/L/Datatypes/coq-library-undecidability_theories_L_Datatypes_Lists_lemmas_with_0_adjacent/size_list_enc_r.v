From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L Require Import Functions.EqBool.
From Undecidability.L.Datatypes Require Import LBool LNat LOptions LProd.
From Undecidability.L Require Import UpToC.
From Undecidability.L.Datatypes.List Require List_enc.
Include List_enc.
From Undecidability.L.Datatypes.List Require Export List_basics List_eqb List_extra List_fold List_in List_nat.
Definition c__listsizeCons := 5.
Definition c__listsizeNil := 4.

Lemma size_list_enc_r {X} `{registered X} (l:list X): length l <= size (enc l).
Proof.
rewrite size_list.
induction l;cbn.
all: unfold c__listsizeNil, c__listsizeCons in *; lia.

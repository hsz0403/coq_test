From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L Require Import Functions.EqBool.
From Undecidability.L.Datatypes Require Import LBool LNat LOptions LProd.
From Undecidability.L Require Import UpToC.
From Undecidability.L.Datatypes.List Require List_enc.
Include List_enc.
From Undecidability.L.Datatypes.List Require Export List_basics List_eqb List_extra List_fold List_in List_nat.
Definition c__listsizeCons := 5.
Definition c__listsizeNil := 4.

Lemma size_list_cons (X : Type) (H : registered X) x (l : list X): size (enc (x::l)) = size (enc x) + size (enc l) + c__listsizeCons.
Proof.
rewrite !size_list.
cbn.
lia.

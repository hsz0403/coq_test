From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L Require Import Functions.EqBool.
From Undecidability.L.Datatypes Require Import LBool LNat LOptions LProd.
From Undecidability.L Require Import UpToC.
From Undecidability.L.Datatypes.List Require List_enc.
Include List_enc.
From Undecidability.L.Datatypes.List Require Export List_basics List_eqb List_extra List_fold List_in List_nat.
Definition c__listsizeCons := 5.
Definition c__listsizeNil := 4.

Lemma size_list_In X {R__X :registered X} (x:X) xs: x el xs -> L_facts.size (enc x) <= L_facts.size (enc xs).
Proof.
intro H.
rewrite !size_list,sumn_map_add.
rewrite <- (sumn_le_in (in_map _ _ _ H)) at 1.
nia.

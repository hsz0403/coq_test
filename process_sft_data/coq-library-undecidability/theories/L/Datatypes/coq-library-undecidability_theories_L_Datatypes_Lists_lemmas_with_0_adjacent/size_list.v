From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L Require Import Functions.EqBool.
From Undecidability.L.Datatypes Require Import LBool LNat LOptions LProd.
From Undecidability.L Require Import UpToC.
From Undecidability.L.Datatypes.List Require List_enc.
Include List_enc.
From Undecidability.L.Datatypes.List Require Export List_basics List_eqb List_extra List_fold List_in List_nat.
Definition c__listsizeCons := 5.
Definition c__listsizeNil := 4.

Lemma size_list X `{registered X} (l:list X): size (enc l) = sumn (map (fun x => size (enc x) + c__listsizeCons) l)+ c__listsizeNil.
Proof.
change (enc l) with (list_enc l).
unfold c__listsizeCons, c__listsizeNil.
induction l.
-
easy.
-
cbn [list_enc map sumn size].
change ((match H with | @mk_registered _ enc _ _ => enc end a)) with (enc a).
solverec.

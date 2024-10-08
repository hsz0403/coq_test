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
Admitted.

Lemma size_list_cons (X : Type) (H : registered X) x (l : list X): size (enc (x::l)) = size (enc x) + size (enc l) + c__listsizeCons.
Proof.
rewrite !size_list.
cbn.
Admitted.

Lemma size_rev X {_:registered X} (xs : list X): L_facts.size (enc (rev xs)) = L_facts.size (enc xs).
Proof.
rewrite !size_list,map_rev,<- sumn_rev.
Admitted.

Lemma size_list_enc_r {X} `{registered X} (l:list X): length l <= size (enc l).
Proof.
rewrite size_list.
induction l;cbn.
Admitted.

Lemma size_list_In X {R__X :registered X} (x:X) xs: x el xs -> L_facts.size (enc x) <= L_facts.size (enc xs).
Proof.
intro H.
rewrite !size_list,sumn_map_add.
rewrite <- (sumn_le_in (in_map _ _ _ H)) at 1.
nia.

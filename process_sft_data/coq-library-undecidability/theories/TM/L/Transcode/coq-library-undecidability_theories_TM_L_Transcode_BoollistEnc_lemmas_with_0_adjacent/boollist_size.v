From Undecidability.L Require Import LTactics Datatypes.Lists Datatypes.LNat Datatypes.LBool.
From Undecidability.TM Require TM.
From Undecidability.TM Require Import TM_facts SizeBounds.
From Undecidability.L.Complexity Require Import UpToCNary.
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
Unset Printing Coercions.
From Undecidability.TM.L Require Alphabets.
From Coq Require Import Lia Ring Arith.
From Undecidability Require Import TM.Code.List.Concat_Repeat.
Definition enc_bool_perElem (b:bool) := [lamT;lamT;varT 0;lamT; lamT; varT (if b then 1 else 0); retT; retT;appT].
Definition enc_bool_nil := [lamT; lamT; varT 1; retT; retT].
Definition enc_bool_closing := [appT; retT; retT].
Arguments enc_bool_perElem : simpl never.
Arguments enc_bool_nil : simpl never.
Arguments enc_bool_closing : simpl never.

Lemma boollist_size :( fun (bs:list bool) => Code.size bs) <=c (fun bs => length bs + 1).
Proof.
eexists.
intros bs.
rewrite size_list.
erewrite (MoreBase.sumn_map_le_pointwise (f2:=fun _ => _)).
2:{
intros [] ?;cbv.
all:reflexivity.
}
setoid_rewrite MoreList.sumn_map_c.
instantiate (1:=2).
nia.

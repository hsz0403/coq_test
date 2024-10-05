From Undecidability.L Require Import LTactics Datatypes.Lists Datatypes.LNat Datatypes.LBool.
From Undecidability.TM Require TM ProgrammingTools CaseList CaseBool ListTM.
From Undecidability.TM Require Import TM_facts SizeBounds L.Transcode.BoollistEnc.
From Undecidability.L.Complexity Require Import UpToCNary.
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
Unset Printing Coercions.
From Undecidability.TM.L Require Alphabets.
From Coq Require Import Lia Ring Arith.
From Undecidability Require Import TM.Code.List.Concat_Repeat.
From Undecidability Require Import Cons_constant CaseCom CaseNat CaseList.
Set Default Proof Using "Type".
Module EncToBoollist.
Section M.
Import ProgrammingTools Combinators App CaseList CaseBool.
Import Alphabets.
Variable (sig : finType).
Context `{retr__list : Retract (sigList bool) sig} `{retr__Pro : Retract Alphabets.sigPro sig}.
Local Instance retr__nat : Retract sigNat sig := ComposeRetract retr__Pro _.
Local Instance retr__bool : Retract bool sig := ComposeRetract retr__list (Retract_sigList_X _).
Definition M__step : pTM sig^+ (option unit) 3 := CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];; CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];; CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];; CaseCom ⇑ ComposeRetract retr__Pro _ @ [|Fin2|];; If (CaseNat ⇑ _ @ [|Fin2|]) (Return (Reset _ @ [|Fin2|];; CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];; CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|] ) (Some tt)) (Reset _ @ [|Fin2|];; CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];; CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];; CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];; CaseCom ⇑ ComposeRetract retr__Pro _ @ [|Fin2|];; Switch (CaseNat ⇑ _ @ [|Fin2|]) (fun b => Cons_constant.M b ⇑ retr__list @[|Fin1|]);; Reset _ @ [|Fin2|];; CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];; CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];; CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];; Return Nop (None) ).
Import Hoare.
Arguments rcomp : simpl never.
Definition M__loop : pTM sig^+ unit 3 := While M__step.
Import ListTM.
Definition M : pTM sig^+ unit 3 := WriteValue ( (nil:list bool)) ⇑ _ @ [|Fin1|];; M__loop.
End M.
End EncToBoollist.
Arguments EncToBoollist.M : clear implicits.
Arguments EncToBoollist.M {_} _ _.

Lemma SpecT__step : { f : UpToC (fun bs => 1) & forall (bs res :list bool) (n:nat), TripleT ≃≃([],[|Contains _ (flat_map enc_bool_perElem bs ++ enc_bool_nil ++ concat (repeat enc_bool_closing n)); Contains _ res;Void|]) (f bs) M__step (fun y => ≃≃([y = match bs with [] => Some tt | _ => None end] ,match bs with | [] => [| Contains _ (concat (repeat enc_bool_closing (n + length bs)));Contains _ res;Void |] | b::bs' => [|Contains _ (flat_map enc_bool_perElem bs' ++ enc_bool_nil ++ concat (repeat enc_bool_closing n));Contains _ (b::res);Void|] end)) }.
Proof.
evar (c1 : nat);evar (c2 :nat).
exists_UpToC (fun bs => max c1 c2).
2:now smpl_upToC_solve.
intros bs res n.
unfold M__step.
rewrite app_assoc,enc_boollist_helper.
hstep.
3:shelve.
now (hsteps_cbn;cbn;tspec_ext).
cbn.
hintros ? ->.
do 5 ((hstep;cbn);[hsteps_cbn;cbn;tspec_ext| cbn;hintros;first [ intros ? ->|intros ** ] |reflexivity]).
clear H.
refine (_ : TripleT _ (match bs with [] => _ | _ => _ end) _ _).
hstep.
-
cbn;hsteps_cbn.
tspec_ext.
cbn.
eassumption.
-
cbn.
destruct bs; hintros ?.
2:nia.
hsteps_cbn.
now tspec_ext.
2-3:reflexivity.
cbn.
hintros ? ->.
hsteps_cbn;cbn.
tspec_ext.
cbn.
2-3:reflexivity.
hintros ? ->.
now hsteps_cbn.
cbn.
rewrite Nat.add_0_r.
tspec_ext.
-
cbn.
refine (_ : TripleT _ match bs with [] => _ | b::bs => _ end _ _).
destruct bs; hintros ?.
nia.
hsteps_cbn.
now tspec_ext.
2-3:unfold CaseList_steps; cbn;reflexivity.
cbn.
hintros ? ->.
hsteps_cbn.
now tspec_ext.
2-3:unfold CaseList_steps; cbn;reflexivity.
cbn.
hintros ? ->.
hsteps_cbn.
now tspec_ext.
3:reflexivity.
2:{
unfold CaseList_steps,CaseList_steps_cons.
rewrite Encode_Com_hasSize.
unfold Encode_Com_size.
rewrite Encode_sum_hasSize;cbn -["+" "*"].
set (m := length _).
assert (m<= 2) by now (subst m;destruct b;cbn).
rewrite H0.
reflexivity.
}
cbn.
hintros ? ->.
hsteps_cbn;cbn.
now tspec_ext.
2:reflexivity.
hintros y Hy.
destruct y.
{
exfalso.
destruct a;inv Hy.
}
destruct Hy as (?&[=<-]).
hsteps_cbn;cbn.
now tspec_ext.
2,6,7,8:reflexivity.
{
hintros y Hy.
replace y with b.
2:{
destruct b,y;cbn in Hy.
all:easy.
}
clear Hy.
hsteps_cbn;cbn.
tspec_ext.
}
{
cbn.
hsteps_cbn.
}
{
cbn.
hsteps_cbn.
cbn.
reflexivity.
}
cbn.
hintros ? ->.
hsteps_cbn.
now tspec_ext.
2,3:unfold CaseList_steps;cbn;reflexivity.
cbn.
hintros ? ->.
hsteps_cbn.
now tspec_ext.
2,3:unfold CaseList_steps;cbn;reflexivity.
cbn.
hintros ? ->.
hsteps_cbn.
2:reflexivity.
tspec_ext.
f_equal.
unfold enc_bool_nil;cbn;autorewrite with list .
reflexivity.
-
cbn - ["+" "*"].
intros b Hb.
destruct b,bs; try (exfalso;nia).
all:reflexivity.
Unshelve.
3:{
destruct bs.
+
rewrite <- Nat.le_max_r.
now cbv.
+
rewrite <- Nat.le_max_l.
unfold Cons_constant.time,CaseList_steps,Reset_steps.
ring_simplify.
unshelve erewrite (_ : size (Init.Nat.pred (if b then 1 else 0))<= 1).
{
now destruct b;cbv.
}
unshelve erewrite (_ : size b<= 1).
{
now destruct b;cbv.
}
unfold c1.
reflexivity.
}
exact 0.

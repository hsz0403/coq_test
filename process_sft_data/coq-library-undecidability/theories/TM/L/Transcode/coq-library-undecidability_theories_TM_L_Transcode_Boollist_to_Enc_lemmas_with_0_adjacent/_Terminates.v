From Undecidability.L Require Import LTactics Datatypes.Lists Datatypes.LNat Datatypes.LBool.
From Undecidability.TM Require TM ProgrammingTools CaseList CaseBool ListTM.
From Undecidability.TM Require Import TM_facts SizeBounds L.Transcode.BoollistEnc Hoare.
From Undecidability.L.Complexity Require Import UpToCNary.
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
Unset Printing Coercions.
From Undecidability.TM.L Require Alphabets.
From Coq Require Import Lia Ring Arith.
From Undecidability Require Import TM.Code.List.Concat_Repeat.
Set Default Proof Using "Type".
Module BoollistToEnc.
Section M.
Import ProgrammingTools Combinators App CaseList CaseBool.
Import Alphabets.
Variable (sig : finType).
Context `{retr__list : Retract (sigList bool) sig} `{retr__Pro : Retract Alphabets.sigPro sig}.
Local Instance retr__nat : Retract sigNat sig := ComposeRetract retr__Pro _.
Local Instance retr__bool : Retract bool sig := ComposeRetract retr__list (Retract_sigList_X _).
Definition Rel : pRel sig^+ unit 4 := ignoreParam (fun tin 'tout => forall (bs : list bool), tin[@Fin0] ≃ bs -> isVoid tin[@Fin1] -> isVoid tin[@Fin2] -> isVoid tin[@Fin3] -> isVoid tout[@Fin0] /\ tout[@Fin1] ≃ compile (Computable.enc (rev bs)) /\ isVoid tout[@Fin2] /\ isVoid tout[@Fin3]).
Definition M__step : pTM sig^+ (option unit) 4 := If (LiftTapes (ChangeAlphabet (CaseList.CaseList _) retr__list) [|Fin0;Fin2|]) (Switch (LiftTapes (ChangeAlphabet CaseBool retr__bool) [|Fin2|]) (fun b => LiftTapes (ChangeAlphabet (WriteValue ( (enc_bool_perElem b))) _) [| Fin2|];; LiftTapes (ChangeAlphabet (App' _) _) [|Fin2;Fin1|];; Return (LiftTapes (Reset _) [|Fin2|]) None)) (Return (LiftTapes (Reset _) [|Fin0|]) (Some tt)).
Definition Rel__step : pRel sig^+ (option unit) 4 := (fun tin '(yout,tout) => forall (bs : list bool) (res : Pro), tin[@Fin0] ≃ bs -> tin[@Fin1] ≃ res -> isVoid tin[@Fin2] -> match bs,yout with [], Some _ => isVoid tout[@Fin0] /\ tout[@Fin1] = tin[@Fin1] | (b::bs),None => tout[@Fin0] ≃ bs /\ tout[@Fin1] ≃ enc_bool_perElem b++res | _,_ => False end /\ isVoid tout[@Fin2] /\ tout[@Fin3] = tin[@Fin3]).
Definition Ter' time: tRel sig^+ 4 := (fun tin k => exists (bs : list bool) (res : Pro), tin[@Fin0] ≃ bs /\ tin[@Fin1] ≃ res /\ isVoid tin[@Fin2] /\ time (length bs) <= k ).
Import MoreList.
Definition Terminates__step := projT2 _Terminates__step.
Definition M__loop : pTM sig^+ unit 4 := While M__step.
Definition Rel__loop : pRel sig^+ (unit) 4 := (fun tin '(yout,tout) => forall (bs : list bool) (res : Pro), tin[@Fin0] ≃ bs -> tin[@Fin1] ≃ res -> isVoid tin[@Fin2] -> isVoid tout[@Fin0] /\ tout[@Fin1] ≃ flat_map enc_bool_perElem (rev bs)++res /\ isVoid tout[@Fin2] /\ tout[@Fin3] = tin[@Fin3]).
Import MoreList.
Definition Terminates__loop := projT2 _Terminates__loop.
Import ListTM.
Definition M : pTM sig^+ unit 4 := LiftTapes (Length retr__list retr__nat) [|Fin0;Fin3;Fin1;Fin2|];; (*0: still bs, 3:length bs, 1,2:right *) LiftTapes (ChangeAlphabet (WriteValue ( ([] : Pro))) retr__Pro) [|Fin1|];; (* 1:res *) LiftTapes (ChangeAlphabet (WriteValue ( (enc_bool_closing))) retr__Pro) [|Fin2|];; (* 2:const for repeat *) LiftTapes (ConcatRepeat.M retr__Pro retr__nat) [|Fin2;Fin3;Fin1|];; (* 2:cnst for repeat, 3:length/empty, 1:res *) LiftTapes (Reset _) [|Fin2|];;(*2: empty*) LiftTapes (ChangeAlphabet (WriteValue ( (enc_bool_nil))) retr__Pro ) [|Fin2|];;(*2:nil*) LiftTapes (ChangeAlphabet (App' _) retr__Pro) [|Fin2;Fin1|];;(* 1 : res with nil part *) LiftTapes (Reset _) [|Fin2|];;(*2: empty*) M__loop.
Definition Ter time: tRel sig^+ 4 := (fun tin k => exists (bs : list bool), tin[@Fin0] ≃ bs /\ isVoid tin[@Fin1] /\ isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\ time (length bs) <= k ).
Definition Terminates := projT2 _Terminates.
End M.
End BoollistToEnc.
Arguments BoollistToEnc.M : clear implicits.
Arguments BoollistToEnc.M {_} _ _.

Lemma _Terminates : { time : UpToC (fun l => l + 1) & projT1 M ↓ Ter time}.
Proof.
eexists_UpToC time.
eapply TerminatesIn_monotone.
{
unfold M.
TM_Correct.
all: eauto 2 using App'_Terminates,App'_Realise,Length_Computes,ConcatRepeat.Realise,ConcatRepeat.Terminates,Length_Terminates,Realise__loop.
simple apply Terminates__loop.
}
intros tin k H.
hnf in H.
destruct H as (bs&Hbs&Hres&Htin2&Htin3&Hl).
cbn -[plus].
infTer 3.
{
unfold Length_T.
cbn.
eexists.
repeat simple apply conj.
now contains_ext.
1-3:now isVoid_mono.
rewrite (correct__leUpToC (Length_steps_nice _) bs),(correct__leUpToC boollist_size).
reflexivity.
}
2:{
intros tout _ (H&Hrem).
TMSimp.
modpon H.
infTer 5.
intros t1_ _ (Ht1&Ht1Rem).
TMSimp.
modpon Ht1;[].
infTer 5.
intros t2_ _ (Ht2&Ht2Rem).
TMSimp.
modpon Ht2;[].
unfold ConcatRepeat.Ter.
cbn.
infTer 5.
1:{
repeat simple apply conj.
1,2,3:now contains_ext.
rewrite UpToC_le.
reflexivity.
}
intros t3_ _ (Ht3&Ht3Rem).
TMSimp.
modpon Ht3;[].
rewrite app_nil_r in Ht4.
infTer 4.
1-2:easy.
intros t4 _ (Htp4&Ht4Rem).
TMSimp.
modpon Htp4;[].
infTer 5.
intros t5 _ (Htp5&Ht5Rem).
TMSimp.
modpon Htp5;[].
infTer 5.
1:{
unfold App'_T.
cbn.
eexists _,_.
repeat simple apply conj.
1,2:simpl_surject;now contains_ext.
rewrite (correct__leUpToC (App'_steps_nice _)).
reflexivity.
}
intros t6_ _ Ht6.
modpon Ht6;[].
TMSimp.
infTer 4.
now contains_ext.
{
unfold Reset_steps.
reflexivity.
}
intros t7 _ Htp7.
modpon Htp7;[].
hnf.
TMSimp.
do 2 eexists.
repeat simple apply conj.
1,2:now contains_ext.
now isVoid_mono.
rewrite UpToC_le.
reflexivity.
}
-
rewrite <- Hl.
set (l:=length bs).
[time]:intros l.
unfold time.
reflexivity.
-
unfold time.
solve [smpl_upToC_solve].

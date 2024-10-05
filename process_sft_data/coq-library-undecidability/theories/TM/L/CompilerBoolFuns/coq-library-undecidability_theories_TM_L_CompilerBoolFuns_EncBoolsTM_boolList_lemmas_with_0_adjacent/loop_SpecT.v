From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
From Undecidability.L Require Import L_facts UpToC.
From Coq Require Vector.
Import ListNotations.
From Coq Require Import List.
From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec.
Require Import Equations.Type.DepElim.
From Undecidability.TM Require Import TM_facts Hoare ProgrammingTools.
From Undecidability.TM.Code Require Import CaseBool CaseList WriteValue Copy ListTM.
Set Default Proof Using "Type".
Module Boollist2encBoolsTM.
Section Fix.
Variable Σ : finType.
Variable s b : Σ^+.
Variable (retr_list : Retract (sigList bool) Σ).
Local Instance retr_bool : Retract bool Σ := ComposeRetract retr_list (Retract_sigList_X _).
Definition M__step : pTM (Σ) ^+ (option unit) 3 := If (CaseList _ ⇑ retr_list @ [|Fin0;Fin2|]) (Switch (CaseBool ⇑ retr_bool @ [|Fin2|]) (fun x => WriteMove (if x then s else b) Lmove @ [|Fin1|];; Return Nop None)) (Reset _ @[|Fin0|];;Return (Write b @ [|Fin1|]) (Some tt)).
Definition M__loop := While M__step.
Definition M : pTM (Σ) ^+ unit 3 := (*LiftTapes (MoveToSymbol (fun _ => false) id) [|Fin1|];;*) M__loop.
End Fix.
End Boollist2encBoolsTM.
Module encBoolsTM2boollist.
Section Fix.
Variable Σ : finType.
Variable s b : Σ^+.
Variable (retr_list : Retract (sigList bool) Σ).
Local Instance retr_bool : Retract bool Σ := ComposeRetract retr_list (Retract_sigList_X _).
Definition M__step : pTM (Σ) ^+ (option unit) 2 := Switch (ReadChar @ [|Fin0|]) (fun x => match x with None => Return Nop (Some tt) | Some x => Move Lmove @ [|Fin0|];; If (Relabel (ReadChar @ [|Fin0|]) ssrbool.isSome) ((Cons_constant.M (if Dec (x=s) then true else false)) ⇑ retr_list @ [|Fin1|];;Return Nop (None)) (Return (Move Rmove @ [|Fin0|]) (Some tt)) end).
Definition M__loop := While M__step.
Definition M : pTM (Σ) ^+ unit 2 := (MoveToSymbol (fun _ => false) (fun x => x);;Move Lmove) @ [|Fin0|];; WriteValue (@nil bool)⇑ retr_list @ [|Fin1|];; M__loop.
End Fix.
End encBoolsTM2boollist.

Lemma loop_SpecT (H__neq : s <> b): { f : UpToC (fun bs => length bs + 1) & forall bs res tin, TripleT (≃≃([right tin = map (fun (x:bool) => if x then s else b) res /\ tape_local_l tin = (map (fun (x:bool) => if x then s else b) bs++[b]) ],[| Custom (eq tin); Contains _ res|]) ) (f bs) M__loop (fun _ => ≃≃([],[|Custom (eq (encBoolsTM s b (rev bs++res))) ; Contains _ (rev bs ++ res)|])) }.
Proof.
evar (c1 : nat);evar (c2 :nat).
exists_UpToC (fun bs => c1 * length bs + c2).
2:now smpl_upToC_solve.
intros bs res tin.
unfold M__loop.
eapply While_SpecTReg with (PRE := fun '(bs,res,tin) => (_,_)) (INV := fun '(bs,res,tin) y => ([match y with None => bs <> nil | _ => bs = nil end; right tin = map (fun (x:bool) => if x then s else b) res; tape_local_l tin = (map (fun (x:bool) => if x then s else b) bs++[b])], match bs with nil => [|Custom (eq tin) ; Contains _ res|] | b'::bs => [|Custom (eq (tape_move_left tin));Contains _ (b'::res)|] end)) (POST := fun '(bs,res,tin) y => (_,_)) (f__step := fun '(bs,res,tin) => _) (f__loop := fun '(bs,res,tin) => _) (x := (bs,res,tin)); clear bs res tin; intros [[bs res] tin]; cbn in *.
{
unfold M__step.
hintros [Hres Hbs].
hsteps_cbn;cbn.
2:reflexivity.
cbn.
intros y.
hintros (?&->&<-).
assert (Hcur : current tin = Some (hd s (map (fun x : bool => if x then s else b) bs ++ [b]))).
{
destruct bs;cbn in Hbs.
all:now eapply tape_local_l_current_cons in Hbs as ->.
}
setoid_rewrite Hcur at 2;cbn.
hstep;cbn.
now hsteps_cbn.
2:reflexivity.
cbn;intros _.
hstep.
{
hsteps_cbn;cbn.
intros yout.
hintros (?&Hy&?&->&_&<-).
set (y:=@ssrbool.isSome (boundary + Σ) yout).
refine (_ : Entails _ ≃≃([ y=match bs with [] => false | _ => true end],_)).
subst y yout.
tspec_ext.
destruct bs;cbn in Hbs;eapply tape_local_l_move_left in Hbs;cbn in Hbs.
now destruct (tape_move_left tin);cbn in Hbs|-*;congruence.
destruct bs;cbn in Hbs;eapply tape_local_l_current_cons in Hbs.
all:now rewrite Hbs.
}
2:{
destruct bs;hintros [=];[].
cbn in *.
hsteps_cbn.
tspec_ext.
1-2:assumption.
destruct H0 as (?&?&?&?&->&?&<-).
rewrite H0.
erewrite tape_move_left_right.
all:easy.
}
{
destruct bs;hintros [=];[].
cbn in *.
hsteps.
{
tspec_ext;cbn in *.
contains_ext.
}
{
intros.
hsteps_cbn.
tspec_ext.
1-3:easy.
2:now destruct H0 as (?&?&?&?&?);congruence.
f_equal.
destruct b0;decide _.
all:congruence.
}
cbv.
reflexivity.
}
cbn.
intros ? ->.
destruct bs.
2:reflexivity.
nia.
}
split.
-
intros [Hres Hbs] _;cbn.
split.
2:{
cbn.
[c2]:exact 14.
subst c2.
nia.
}
destruct bs as [ | ];cbn.
2:easy.
apply midtape_tape_local_l_cons in Hbs.
rewrite Hres in Hbs.
rewrite Hbs.
reflexivity.
-
intros H.
destruct bs as [ | b' bs].
easy.
intros Hres Hbs.
cbn in Hbs.
apply midtape_tape_local_l_cons in Hbs.
rewrite Hres in Hbs.
eexists ((bs,b'::res),tape_move_left tin).
repeat eapply conj.
+
cbn.
erewrite tape_right_move_left.
2:subst;reflexivity.
erewrite tape_local_l_move_left.
2:subst;reflexivity.
rewrite Hres.
tspec_ext.
easy.
+
subst c2;cbn;ring_simplify.
[c1]:exact 15.
unfold c1;nia.
+
cbn.
rewrite <- !app_assoc.
reflexivity.

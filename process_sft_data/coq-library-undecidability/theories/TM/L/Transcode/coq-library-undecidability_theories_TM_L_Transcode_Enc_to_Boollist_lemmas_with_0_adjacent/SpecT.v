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

Lemma SpecT : { f : UpToC (fun bs => length bs + 1) & forall (bs :list bool), TripleT ≃≃([],[|Contains _ (compile (Computable.enc bs)); Void;Void|]) (f bs) M (fun _ => ≃≃([],[| Contains _ (concat (repeat enc_bool_closing (length bs)));Contains _ (rev bs);Void |]))}.
Proof.
unfold M.
eexists_UpToC f.
intros.
rewrite enc_bool_explicit.
hsteps_cbn;cbn.
reflexivity.
{
eapply ConsequenceT.
eapply (projT2 SpecT__loop) with (n:=length bs) (res:=[]).
all:cbn.
now tspec_ext.
now rewrite app_nil_r.
reflexivity.
}
[f]:intros bs.
ring_simplify.
unfold f;reflexivity.
subst f.
smpl_upToC_solve.

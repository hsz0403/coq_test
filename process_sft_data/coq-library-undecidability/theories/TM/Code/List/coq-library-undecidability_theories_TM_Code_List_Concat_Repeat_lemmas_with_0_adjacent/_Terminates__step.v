From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import CaseNat CaseList List.App.
From Undecidability.L.Complexity Require Import UpToCNary.
Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.
Section bla.
Import FinTypes.
Polymorphic Lemma leUpToC_clean domain (f F: Rtuple domain -> nat): Fun' f <=c Fun' F -> f <=c F.
Proof.
prove_nary id.
End bla.
Module ConcatRepeat.
Section concatRepeat.
Variable sig sigX : finType.
Variable (X : Type) (cX : codable sigX X).
Variable (retr1 : Retract (sigList sigX) sig) (retr2 : Retract sigNat sig).
Definition Rel__step : pRel sig^+ (option unit) 3 := fun tin '(yout,tout) => forall (cs : list X) (n:nat) ( xs : list X) , tin[@Fin0] ≃ cs -> tin[@Fin1] ≃ n -> tin[@Fin2] ≃ xs -> match yout, n with | (Some tt), 0 => (* break *) tout[@Fin0] ≃ cs /\ isVoid tout[@Fin1] /\ tout[@Fin2] ≃ xs | None, S n => (* continue *) tout[@Fin0] ≃ cs /\ tout[@Fin1] ≃ n /\ tout[@Fin2] ≃ cs++xs | _, _ => False end.
Definition M__step : pTM sig^+ (option unit) 3 := If (LiftTapes (ChangeAlphabet CaseNat _) [|Fin1|]) (Return (LiftTapes (ChangeAlphabet (App' _) _) [|Fin0; Fin2|]) None) (Return (LiftTapes (Reset _) [|Fin1|]) (Some tt)).
Definition Rel : pRel sig^+ unit 3 := ignoreParam ( fun tin tout => forall (cs : list X) (n:nat) ( xs : list X) , tin[@Fin0] ≃ cs -> tin[@Fin1] ≃ n -> tin[@Fin2] ≃ xs -> tout[@Fin0] ≃ cs /\ isVoid tout[@Fin1] /\ tout[@Fin2] ≃ concat (repeat cs n)++xs ).
Definition M : pTM sig^+ unit 3 := While M__step.
Definition Ter__step time : tRel sig^+ 3 := fun tin k => exists (cs : list X) (n:nat) ( xs : list X) , tin[@Fin0] ≃ cs /\ tin[@Fin1] ≃ n /\ tin[@Fin2] ≃ xs /\ time (n,size cs) <= k.
Definition Terminates__step := projT2 _Terminates__step.
Definition Ter time : tRel sig^+ 3 := fun tin k => exists (cs : list X) (n:nat) ( xs : list X) , tin[@Fin0] ≃ cs /\ tin[@Fin1] ≃ n /\ tin[@Fin2] ≃ xs /\ time (size cs,n) <= k.
Definition Terminates := projT2 _Terminates.
End concatRepeat.
End ConcatRepeat.

Lemma _Terminates__step : { time : UpToC (fun '(n,l) => (if n =? 0 then 0 else l) + 1) & projT1 M__step ↓ Ter__step time}.
Proof.
eexists_UpToC time.
[time]:refine (fun '(n,l) => if n =? 0 then _ else _).
eapply TerminatesIn_monotone.
{
unfold M__step.
TM_Correct.
now apply App'_Terminates with (cX:=cX).
}
{
intros tin k (cs&n&xs&Hcs&Hn&Hxs&Hk).
cbn.
eexists.
eexists (if n =? 0 then _ else _).
infTer 3.
rewrite <- Hk.
2:{
clear Hk time.
intros tout b (HCaseNat&HRem).
modpon HCaseNat.
destruct b.
all:destruct (Nat.eqb_spec n 0) as [Hn0|Hn0].
all:try now (destruct n;exfalso).
2:{
rewrite Hn0 in HCaseNat.
exists 0.
split.
2:reflexivity.
simpl_surject.
TMSimp.
contains_ext.
}
unfold App'_T;cbn.
eexists cs, xs.
TMSimp.
split.
2:split.
3:reflexivity.
all:simpl_surject.
all:contains_ext.
}
unfold CaseNat_steps,Reset_steps.
unfold time.
destruct Nat.eqb.
reflexivity.
rewrite (correct__leUpToC (App'_steps_nice _)).
set (size cs) as l.
reflexivity.
}
unfold time.
apply leUpToC_finCases with (cases := fun (b:bool) => match b return (if b then nat*nat else nat) -> _ with false => fun l => (0,l) | true => fun '(n,l) => (S n, l) end).
{
intros [[ |n] l].
now (exists false; eauto).
now (exists true;eexists (_,_);eauto).
}
intros [].
nary apply leUpToC_clean.
2:{
cbn [fst snd].
rewrite Nat.eqb_refl.
smpl_upToC_solve.
}
cbn [Nat.eqb].
smpl_upToC_solve.

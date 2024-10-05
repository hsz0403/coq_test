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

Lemma Realise__step : M__step ⊨ Rel__step .
Proof.
eapply Realise_monotone.
{
unfold M__step.
TM_Correct.
now apply App'_Realise.
}
intros t (y,t') H.
cbn.
intros cs n xs Hcs Hn Hxs.
cbn in H.
destruct H as [H|H].
-
destruct H as (?&(HCase&HCaseRem)&->&tt1&HApp&HAppRem).
clear tt1.
modpon HCase.
destruct n.
easy.
TMSimp.
modpon HApp.
repeat eapply conj.
1-3:now contains_ext.
-
destruct H as (?&(HCase&HCaseRem)&->&tt1&HReset&HResetRem).
clear tt1.
modpon HCase.
destruct n.
2:easy.
TMSimp.
modpon HReset.
repeat eapply conj.
1,3:now contains_ext.
now isVoid_mono.

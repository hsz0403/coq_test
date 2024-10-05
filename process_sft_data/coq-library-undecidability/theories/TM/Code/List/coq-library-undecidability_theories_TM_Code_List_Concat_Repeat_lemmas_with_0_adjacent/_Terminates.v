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

Lemma _Terminates : {time : UpToC (fun '(l,n) => n * l + 1) & projT1 M ↓ Ter time }.
Proof.
evar (c1 : nat).
evar (c2 : nat).
exists_UpToC (fun '(l,n) => n * l * c1 + c2).
unfold M.
eapply TerminatesIn_monotone.
-
TM_Correct.
now apply Realise__step.
now apply Terminates__step.
-
apply WhileCoInduction.
unfold Ter.
intros tin k (cs&n&xs&Hcs&Hn&Hxs&Hk).
eexists.
unfold Ter__step.
split.
{
exists cs,n,xs.
repeat simple apply conj.
1-3:eassumption.
rewrite UpToC_le.
reflexivity.
}
unfold Rel__step.
intros ymid tmid Hstep.
modpon Hstep.
destruct ymid as [[]| ],n.
all:try now exfalso.
+
rewrite Nat.eqb_refl.
rewrite <- Hk, Nat.mul_0_l, Nat.mul_1_r,!Nat.add_0_l.
unfold c2.
reflexivity.
+
TMSimp.
eexists.
split.
*
repeat simple eapply ex_intro.
repeat simple apply conj.
1-3:contains_ext.
reflexivity.
*
rewrite <- Hk.
ring_simplify.
set (c' := c__leUpToC).
assert (size cs > 0).
1:{
rewrite Encode_list_hasSize.
destruct cs;cbn;nia.
}
replace c1 with (2 + 2*c').
2:now unfold c',c1.
nia.
-
smpl_upToC_solve.

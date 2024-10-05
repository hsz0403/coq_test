From Undecidability.TM Require Import Util.Prelim Code.CodeTM.
From Undecidability.TM Require Import Lifting.LiftAlphabet.
Local Hint Mode Retract - - : typeclass_instances.
Generalizable All Variables.
Section SurjectInject.
Variable (sig tau : Type).
Variable def : sig.
Variable retr : Retract sig tau.
Definition injectSymbols : list sig -> list tau := map Retr_f.
Definition surjectSymbols : list tau -> list sig := map (surject Retr_g def).
End SurjectInject.
Section MapCode.
Variable sig tau : Type.
Variable retr : Retract sig tau.
Variable (sigX X : Type) (cX : codable sigX X) (I_x : Retract sigX sig) (I : Retract sig tau).
Global Instance Retract_plus : Retract (boundary + sig) (boundary + tau) := Retract_sum _ _.
Notation "'f''" := (@Retr_f (boundary+sig) (boundary+tau) Retract_plus).
Notation "'g''" := (@Retr_g (boundary+sig) (boundary+tau) Retract_plus).
Local Arguments Retr_f {X Y} (Retract).
Local Arguments Retr_g {X Y} (Retract).
Local Instance I_x' : Retract sigX tau := ComposeRetract _ _.
Notation injectTape := (mapTape f').
Notation surjectTape := (surjectTape g' (inl UNKNOWN)).
End MapCode.
Hint Unfold surjectTape surjectTapes injectTape : tape.
Arguments Retract_plus : simpl never.
Arguments injectTape : simpl never.
Arguments surjectTape : simpl never.
Section ChangeAlphabet.
Variable (sig tau : finType).
Variable (n : nat) (F : finType).
Variable pM : pTM sig^+ F n.
Variable (retr : Retract sig tau).
Definition ChangeAlphabet : pTM tau^+ F n := LiftAlphabet pM (Retract_plus retr) (inl UNKNOWN).
End ChangeAlphabet.
Notation "pM ⇑ Rmove" := (ChangeAlphabet pM Rmove) (at level 40, only parsing).
Ltac simpl_surject_step := once lazymatch goal with (* encodings *) | [ |- surjectTape _ _ ?t ≃ _ ] => apply contains_translate_tau1 | [ H : surjectTape _ _ ?t ≃ _ |- _ ] => apply contains_translate_tau2 in H | [ |- surjectTape _ _ ?t ≃(;?n) _ ] => apply contains_size_translate_tau1 | [ H : surjectTape _ _ ?t ≃(;?n) _ |- _ ] => apply contains_size_translate_tau2 in H (* [isVoid] and [isVoid_size] *) | [ |- isVoid (surjectTape _ _ ?t) ] => apply surjectTape_isVoid | [ H : isVoid (surjectTape _ _ ?t) |- _ ] => apply surjectTape_isVoid' in H | [ |- isVoid_size (surjectTape _ _ ?t) ?n ] => apply surjectTape_isVoid_size | [ H : isVoid_size (surjectTape _ _ ?t) ?n |- _ ] => apply surjectTape_isVoid'_size in H end.
Ltac simpl_surject := repeat simpl_surject_step.
Ltac smpl_TM_ChangeAlphabet := once lazymatch goal with | [ |- ChangeAlphabet ?pM ?retr ⊨ _ ] => apply LiftAlphabet_Realise | [ |- ChangeAlphabet ?pM ?retr ⊨c(_) _ ] => apply LiftAlphabet_RealiseIn | [ |- projT1 (ChangeAlphabet ?pM ?retr) ↓ _ ] => apply LiftAlphabet_TerminatesIn end.
Smpl Add smpl_TM_ChangeAlphabet : TM_Correct.

Lemma surject_app (str : list tau) (str2 str3 : list sig) : surjectSymbols str = str2 ++ str3 -> exists (str' str'' : list tau), str = str' ++ str'' /\ surjectSymbols str' = str2 /\ surjectSymbols str'' = str3.
Proof.
revert str str3.
induction str2 as [ | s str2 IH]; intros str str3 H; cbn in *.
-
exists nil, str.
cbn.
auto.
-
pose proof surject_cons H as (t&str'&->&L1&L2).
cbn in *.
specialize (IH _ _ L2) as (Str&Str'&->&IH1&IH2).
inv H.
repeat eexists.
instantiate (1 := t :: Str).
reflexivity.
cbn.
reflexivity.

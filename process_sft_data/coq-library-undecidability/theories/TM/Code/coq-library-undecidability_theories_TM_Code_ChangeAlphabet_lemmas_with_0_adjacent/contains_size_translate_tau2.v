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

Lemma contains_size_translate_tau2 (x : X) (s : nat) (t : tape (boundary+tau)) : surjectTape t ≃(;s) x -> t ≃(;s) x.
Proof.
intros (r1&HCode&Hs).
cbn in *.
eapply mapTape_inv_midtape in HCode as (ls'&m'&rs'&->&->&HCode1&HCode2).
repeat econstructor; cbn in *.
f_equal.
-
unfold surject in HCode1.
destruct m'; cbn in *.
cbv [id] in *.
now inv HCode1.
destruct (Retr_g I t); inv HCode1.
-
symmetry in HCode2.
change (surjectSymbols (inl UNKNOWN) Retract_plus rs' = map inr (Encode_map cX _ x) ++ [inl STOP]) in HCode2.
eapply surject_app in HCode2 as (str1&str2&->&L1&L2).
eapply inject_surject in L1 as ->; eauto.
eapply inject_surject in L2 as ->; eauto.
+
f_equal.
unfold injectSymbols.
cbn.
rewrite !map_map.
eapply List.map_ext.
intros.
cbn.
reflexivity.
+
unfold surjectSymbols in L2.
eapply map_eq_cons in L2 as (t & ? & -> & ? & -> % map_eq_nil').
unfold surject in H.
destruct t; cbn in *; swap 1 2.
destruct (Retr_g I t); inv H.
inv H.
intros [ | ]; intros [ | ]; try congruence; auto.
inv H.
eexists.
cbn.
reflexivity.
+
intros [ | ]; intros He; cbn; eauto.
destruct (Retr_g I t) eqn:E1; cbn; eauto.
exfalso.
pose proof surject_inject_inr L1 as (str1'&->&L3).
apply in_map_iff in He as (?&HETmp&HE); inv HETmp.
enough (t el (Encode_map cX _ x)) as L4.
{
pose proof in_encode_retract L4 as (?&?).
congruence.
}
cbn in *.
assert (None el map (Retr_g I) str1') as L5.
{
rewrite <- E1.
eapply in_map_iff; eauto.
}
rewrite L3 in L5.
apply in_map_iff in L5 as (?&?&?).
congruence.
-
now rewrite map_length in Hs.

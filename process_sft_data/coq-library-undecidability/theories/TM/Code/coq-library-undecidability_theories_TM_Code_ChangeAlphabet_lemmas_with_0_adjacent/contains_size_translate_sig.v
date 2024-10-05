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

Lemma contains_size_translate_sig (s : nat) (x : X) (t : tape (boundary+sig)) : t ≃(;s) x <-> (injectTape t) ≃(;s) x.
Proof.
split; intros (r1&HCode&Hs); subst; cbn in *; hnf.
-
repeat eexists.
cbn.
f_equal.
rewrite map_app, !List.map_map.
cbn.
reflexivity.
now simpl_list.
-
unfold injectTape in HCode.
exists (surjectSymbols (inl UNKNOWN) _ r1).
apply mapTape_inv_midtape in HCode as (ls'&m'&rs'&->&->&HCode1&HCode2).
rewrite map_map in HCode2.
destruct m'; cbn in *; inv HCode1.
split.
f_equal.
+
unfold surjectSymbols.
rewrite map_map.
rewrite <- map_id at 1.
eapply List.map_ext.
intros [ | ]; cbn.
reflexivity.
unfold surject.
cbn.
retract_adjoint.
reflexivity.
+
symmetry.
eapply map_injective with (f := retract_sum_f id (Retr_f _)); eauto.
{
intros.
eapply retract_f_injective; eauto.
}
now rewrite map_app, !map_map.
+
unfold surjectSymbols.
rewrite map_length in Hs.
simpl_list.
lia.

From Undecidability Require Import Hoare.HoareLogic.
From Undecidability.TM Require Import TMTac.
From Undecidability.TM Require Export CodeTM LiftTapes ChangeAlphabet.
Section RegSpec.
Variable sig : Type.
Local Notation "sig '^+'" := ((boundary + sig) % type) (at level 0) : type_scope.
Inductive RegSpec : Type := | Contains {sigX X : Type} {cX : codable sigX X} (r : Retract sigX sig) : X -> RegSpec | Contains_size {sigX X : Type} {cX : codable sigX X} (r : Retract sigX sig) : X -> nat -> RegSpec | Void : RegSpec | Void_size : nat -> RegSpec | Custom : (tape sig^+ -> Prop) -> RegSpec.
Definition tspec_single (spec : RegSpec) (t : tape sig^+) : Prop := match spec with | Contains r x => t ≃(r) x | Contains_size r x s => t ≃(r; s) x | Void => isVoid t | Void_size s => isVoid_size t s | Custom p => p t end.
Definition SpecV n := Vector.t (RegSpec) n.
Definition Spec n :Type := list Prop * SpecV n.
Definition tspec {n : nat} (spec : Spec n) : Assert sig^+ n := match spec with | (P,spec) => fun (t : tapes sig^+ n) => List.fold_right and (forall (i : Fin.t n), tspec_single spec[@i] t[@i]) P end.
Arguments tspec : simpl never.
Definition withSpace_single (P : RegSpec) (size : nat) := match P with | Contains r x => Contains_size r x size | Void => Void_size size | _ => P end.
Definition withSpace {n : nat} (P : SpecV n) (spaces : Vector.t nat n) : SpecV n := Vector.map2 withSpace_single P spaces.
Definition dummy_size (t : tape sig^+) (P : RegSpec) : nat := match P with | Contains r x => length (left t) | Void => length (tape_local_l t) | _ => 0 end.
Definition dummy_sizes (n : nat) (t : tapes sig^+ n) (P : SpecV n) : Vector.t nat n := Vector.map2 dummy_size t P.
End RegSpec.
Arguments Custom {sig}.
Arguments Void {sig}.
Arguments Void_size {sig}.
Arguments dummy_sizes : simpl never.
Hint Resolve tspec_single_Contains_size_Contains : core.
Declare Scope spec_scope.
Delimit Scope spec_scope with spec.
Bind Scope spec_scope with Spec.
Notation "'≃≃(' S ')'" := (tspec S%spec) (at level 0, S at level 200, no associativity, format "'≃≃(' S ')'").
Notation "'≃≃(' P ',' S ')'" := (tspec (P%list,S%vector)) (at level 0, P at level 200, S at level 200, no associativity, format "'≃≃(' P ',' S ')'").
Notation "t ≃≃ S" := (tspec S%spec t) (at level 70, no associativity).
Notation "≃( I ) x" := (Contains I x) (at level 70, I at level 200, no associativity, format "'≃(' I ')' x").
Notation "≃( I ';' s ) x" := (Contains_size I s x) (at level 70, I at level 200, s at level 200, no associativity, format "'≃(' I ';' s ')' x").
Arguments tspec _%spec _.
Fixpoint implList (Ps : list Prop) (Q : Prop) := match Ps with [] => Q | P::Ps => P -> implList Ps Q end.
Arguments implList !_ _.
Instance fold_right_impl' : Proper (Forall2 Basics.impl --> Basics.impl ==> Basics.impl) (implList).
Proof.
intros xs;induction xs;cbn;intros ? H';inv H';cbn.
easy.
firstorder.
Instance fold_right_iff : Proper (Forall2 iff ==> iff ==> iff) (implList).
Proof.
intros xs;induction xs;cbn;intros ? H';inv H';cbn.
easy.
firstorder.
Instance Forall2_refl X (R: X -> _): Reflexive R -> Reflexive (Forall2 R).
Proof.
intros ? xs;induction xs;eauto.
Definition SpecVTrue {sig : Type} {n : nat} : SpecV sig n := Vector.const (Custom (fun _ => True)) n.
Arguments tspec : simpl never.
Definition appSize {n : nat} : Vector.t (nat->nat) n -> Vector.t nat n -> Vector.t nat n := fun fs s => tabulate (fun i => fs[@i] s[@i]).
Instance fold_right_and : Proper (iff ==> Forall2 iff ==> iff) (fold_right and).
Proof.
intros ? ? ? xs;induction xs;cbn;intros ? H';inv H';cbn.
easy.
firstorder.
Instance fold_right_and' : Proper (Basics.impl ==> Forall2 iff ==> Basics.impl) (fold_right and).
Proof.
intros ? ? ? xs;induction xs;cbn;intros ? H';inv H';cbn.
easy.
firstorder.
Section Lifting.
Variable (sig : Type).
Variable (m n : nat).
Variable (P : @SpecV sig n).
Variable (I : Vector.t (Fin.t n) m).
Hypothesis (HI : dupfree I).
Definition Downlift : @SpecV sig m := (select I P).
Definition Frame (Q : @SpecV sig m) : @SpecV sig n := fill I P Q.
End Lifting.
Instance dec_ex_fin (n : nat) (P : Fin.t n -> Prop) (decP: forall (i : Fin.t n), dec (P i)) : dec (exists (i : Fin.t n), P i).
Proof.
induction n.
-
right.
intros (i&?).
destruct_fin i.
-
decide (P Fin0).
+
left.
eauto.
+
specialize (IHn (fun i => P (Fin.FS i))).
spec_assert IHn as [IH|IH] by eauto.
*
left.
destruct IH as (i&IH).
exists (Fin.FS i).
eauto.
*
right.
intros (j&H).
pose proof (fin_destruct_S j) as [(j'&->) | ->]; eauto.
Section AlphabetLifting.
Variable (sig tau : Type).
Variable (retr : Retract sig tau).
Definition LiftSpec_single (T : RegSpec sig) : RegSpec tau := match T with | Contains r x => Contains (ComposeRetract retr r) x | Contains_size r x s => Contains_size (ComposeRetract retr r) x s | Void => Void | Void_size s => Void_size s | Custom p => Custom (fun t => p (surjectTape (Retr_g) (inl UNKNOWN) t)) end.
Variable (n : nat).
Definition LiftSpec (T : SpecV sig n) : SpecV tau n := Vector.map LiftSpec_single T.
End AlphabetLifting.
Section AlphabetLifting'.
Variable (sig tau : finType) (n : nat).
Variable (retr : Retract sig tau).
End AlphabetLifting'.
Global Arguments withSpace : simpl never.
Notation "'SpecFalse'" := ([False],_): spec_scope.

Lemma LiftSpec_surjectTapes_tspec' tin P P': surjectTapes Retr_g (inl UNKNOWN) tin ≃≃ (P',P) -> tin ≃≃ (P',LiftSpec P).
Proof.
intros (H'&H)%tspecE.
eapply tspecI.
easy.
unfold LiftSpec in *.
intros i; specialize (H i); cbn.
simpl_tape in *.
Admitted.

Lemma LiftSpec_withSpace_single (sig tau : Type) (I : Retract sig tau) (P : RegSpec sig) (s : nat) : LiftSpec_single I (withSpace_single P s) = withSpace_single (LiftSpec_single I P) s.
Proof.
Admitted.

Lemma LiftSpec_withSpace (sig tau : Type) (n : nat) (I : Retract sig tau) (P : SpecV sig n) (ss : Vector.t nat n) : LiftSpec I (withSpace P ss) = withSpace (LiftSpec I P) ss.
Proof.
eapply VectorSpec.eq_nth_iff; intros ? ? ->.
unfold LiftSpec, withSpace.
simpl_vector.
Admitted.

Lemma ChangeAlphabet_Spec_ex (F : finType) X P' (Ctx : X -> Prop -> Prop) (P : SpecV sig n) (pM : pTM sig^+ F n) Q' (Q : X -> F -> SpecV sig n) : Triple (tspec (P',P)) pM (fun y t => exists x:X, Ctx x (tspec (Q' x y,Q x y) t)) -> (forall x, Proper (Basics.impl ==> Basics.impl) (Ctx x)) -> Triple (tspec (P',LiftSpec retr P)) (ChangeAlphabet pM retr) (fun yout t => exists x, Ctx x (tspec (Q' x yout,LiftSpec retr (Q x yout)) t)).
Proof.
rewrite !Triple_iff.
intros HTrip HCtx.
eapply Realise_monotone.
-
TM_Correct.
eassumption.
-
intros tin (yout, tout) H Henc.
cbn in *.
spec_assert H by now apply LiftSpec_surjectTapes_tspec.
destruct H as (x&H).
exists x.
cbv in HCtx.
eapply HCtx.
2:apply H.
Admitted.

Lemma ChangeAlphabet_Spec (F : finType) P' (P : SpecV sig n) (pM : pTM sig^+ F n) Q' (Q : F -> SpecV sig n) : Triple (tspec (P',P)) pM (fun yout => tspec (Q' yout,Q yout)) -> Triple (tspec (P',LiftSpec retr P)) (ChangeAlphabet pM retr) (fun yout => tspec (Q' yout,LiftSpec retr (Q yout))).
Proof.
rewrite !Triple_iff.
intros HTrip.
eapply Realise_monotone.
-
TM_Correct.
eassumption.
-
intros tin (yout, tout) H Henc.
cbn in *.
spec_assert H by now apply LiftSpec_surjectTapes_tspec.
Admitted.

Lemma ChangeAlphabet_SpecT (F : finType) P' (P : SpecV sig n) (k : nat) (pM : pTM sig^+ F n) Q' (Q : F -> SpecV sig n) : TripleT (tspec (P',P)) k pM (fun yout => tspec (Q' yout, Q yout)) -> TripleT (tspec (P',LiftSpec retr P)) k (ChangeAlphabet pM retr) (fun yout => tspec (Q' yout,LiftSpec retr (Q yout))).
Proof.
intros HTrip.
split.
{
apply ChangeAlphabet_Spec.
eapply TripleT_Triple; eauto.
}
{
eapply TerminatesIn_monotone.
-
TM_Correct.
apply HTrip.
-
unfold Triple_TRel.
intros tin k' (H&Hk).
cbn.
split; auto.
now apply LiftSpec_surjectTapes_tspec.
Admitted.

Lemma ChangeAlphabet_Spec_pre_post (F : finType) P0 (P : SpecV sig n) (P' : SpecV tau n) (pM : pTM sig^+ F n) Q0 (Q : F -> SpecV sig n) (Q' : F -> SpecV tau n) : Triple (tspec (P0,P)) pM (fun yout => tspec (Q0 yout, Q yout) ) -> (Entails ≃≃( P0,P') ≃≃( P0,LiftSpec retr P)) -> (forall yout, Entails ≃≃( Q0 yout, LiftSpec retr (Q yout)) ≃≃( (Q0 yout,Q' yout))) -> Triple (tspec (P0, P')) (ChangeAlphabet pM retr) (fun yout => tspec (Q0 yout, Q' yout)).
Proof.
intros H1 H2 H3.
eapply Consequence.
-
apply ChangeAlphabet_Spec.
apply H1.
-
apply H2.
-
Admitted.

Lemma ChangeAlphabet_SpecT_pre_post (F : finType) P0 (P : SpecV sig n) (P' : SpecV tau n) (k : nat) (pM : pTM sig^+ F n) Q0 (Q : F -> SpecV sig n) (Q' : F -> SpecV tau n) : TripleT (tspec (P0,P)) k pM (fun yout => tspec (Q0 yout, Q yout) ) -> (Entails ≃≃( P0,P') ≃≃( P0,LiftSpec retr P)) -> (forall yout, Entails ≃≃( Q0 yout, LiftSpec retr (Q yout)) ≃≃( (Q0 yout,Q' yout))) -> TripleT (tspec (P0, P')) k (ChangeAlphabet pM retr) (fun yout => tspec (Q0 yout, Q' yout)).
Proof.
intros H1 H2 H3.
eapply ConsequenceT.
-
apply ChangeAlphabet_SpecT.
apply H1.
-
apply H2.
-
apply H3.
-
Admitted.

Lemma ChangeAlphabet_Spec_pre (F : finType) P0 (P : SpecV sig n) (P' : SpecV tau n) (pM : pTM sig^+ F n) Q0 (Q : F -> SpecV sig n) : Triple (tspec (P0,P)) pM (fun yout => tspec (Q0 yout, Q yout)) -> (Entails ≃≃( P0,P') ≃≃( P0, LiftSpec retr P)) -> Triple (tspec (P0,P')) (ChangeAlphabet pM retr) (fun yout => tspec (Q0 yout,LiftSpec retr (Q yout))).
Proof.
intros H1 H2.
eapply Consequence.
-
apply ChangeAlphabet_Spec.
apply H1.
-
apply H2.
-
Admitted.

Lemma ChangeAlphabet_SpecT_pre (F : finType) P0 (P : SpecV sig n) (P' : SpecV tau n) (k : nat) (pM : pTM sig^+ F n) Q0 (Q : F -> SpecV sig n) : TripleT (tspec (P0,P)) k pM (fun yout => tspec (Q0 yout, Q yout)) -> (Entails ≃≃( P0, P') ≃≃( P0,LiftSpec retr P)) -> TripleT (tspec (P0,P')) k (ChangeAlphabet pM retr) (fun yout => tspec (Q0 yout,LiftSpec retr (Q yout))).
Proof.
intros H1 H2.
eapply ConsequenceT.
-
apply ChangeAlphabet_SpecT.
apply H1.
-
apply H2.
-
eauto.
-
Admitted.

Lemma ChangeAlphabet_SpecT_space_pre_post (F : finType) P0 (P : SpecV sig n) (P' : SpecV tau n) (k : nat) (pM : pTM sig^+ F n) Q0 (Q : F -> SpecV sig n) (Q' : F -> SpecV tau n) (ss ss' : Vector.t nat n) : TripleT (tspec (P0,withSpace P ss)) k pM (fun yout => tspec (Q0 yout,withSpace (Q yout) ss')) -> (Entails ≃≃( P0, withSpace P' ss) ≃≃( P0, withSpace (LiftSpec retr P) ss)) -> (forall yout, Entails ≃≃( Q0 yout, withSpace (LiftSpec retr (Q yout)) ss') (tspec (Q0 yout,withSpace (Q' yout) ss'))) -> TripleT (tspec (P0,withSpace P' ss)) k (ChangeAlphabet pM retr) (fun yout => tspec (Q0 yout, withSpace (Q' yout) ss')).
Proof.
intros H1 H2 H3.
eapply ConsequenceT.
-
apply ChangeAlphabet_SpecT.
apply H1.
-
rewrite LiftSpec_withSpace.
apply H2.
-
setoid_rewrite Entails_iff.
cbn.
intros.
rewrite LiftSpec_withSpace in H.
now apply H3.
-
Admitted.

Lemma ChangeAlphabet_Spec_space_pre (F : finType) P0 (P : SpecV sig n) (P' : SpecV tau n) (pM : pTM sig^+ F n) Q0 (Q : F -> SpecV sig n) (ss ss' : Vector.t nat n) : Triple (tspec (P0,withSpace P ss)) pM (fun yout => tspec (Q0 yout,withSpace (Q yout) ss')) -> Entails ≃≃( P0, withSpace P' ss) ≃≃( P0, withSpace (LiftSpec retr P) ss) -> Triple (tspec (P0, withSpace P' ss)) (ChangeAlphabet pM retr) (fun yout => tspec (Q0 yout, withSpace (LiftSpec retr (Q yout)) ss')).
Proof.
intros H1 H2.
eapply Consequence.
-
apply ChangeAlphabet_Spec.
apply H1.
-
rewrite LiftSpec_withSpace.
apply H2.
-
setoid_rewrite Entails_iff.
cbn.
intros.
rewrite LiftSpec_withSpace in H.
Admitted.

Lemma ChangeAlphabet_SpecT_space_pre (F : finType) P0 (P : SpecV sig n) (P' : SpecV tau n) (k : nat) (pM : pTM sig^+ F n) Q0 (Q : F -> SpecV sig n) (ss ss' : Vector.t nat n) : TripleT (tspec (P0,withSpace P ss)) k pM (fun yout => tspec (Q0 yout, withSpace (Q yout) ss')) -> Entails ≃≃( P0, withSpace P' ss) ≃≃( P0, withSpace (LiftSpec retr P) ss) -> TripleT (tspec (P0, withSpace P' ss)) k (ChangeAlphabet pM retr) (fun yout => tspec (Q0 yout,withSpace (LiftSpec retr (Q yout)) ss')).
Proof.
intros H1 H2.
eapply ConsequenceT.
-
apply ChangeAlphabet_SpecT.
apply H1.
-
rewrite LiftSpec_withSpace.
apply H2.
-
setoid_rewrite Entails_iff.
cbn.
intros.
rewrite LiftSpec_withSpace in H.
now apply H.
-
Admitted.

Lemma ChangeAlphabet_Spec_space_pre_post (F : finType) P0 (P : SpecV sig n) (P' : SpecV tau n) (pM : pTM sig^+ F n) Q0 (Q : F -> SpecV sig n) (Q' : F -> SpecV tau n) (ss ss' : Vector.t nat n) : Triple (tspec (P0,withSpace P ss)) pM (fun yout => tspec (Q0 yout,withSpace (Q yout) ss')) -> (Entails ≃≃( P0, withSpace P' ss) ≃≃( P0, withSpace (LiftSpec retr P) ss)) -> (forall yout, Entails ≃≃( Q0 yout, withSpace (LiftSpec retr (Q yout)) ss') (tspec (Q0 yout,withSpace (Q' yout) ss'))) -> Triple (tspec (P0,withSpace P' ss)) (ChangeAlphabet pM retr) (fun yout => tspec (Q0 yout, withSpace (Q' yout) ss')).
Proof.
intros H1 H2 H3.
eapply Consequence.
-
apply ChangeAlphabet_Spec.
apply H1.
-
rewrite LiftSpec_withSpace.
apply H2.
-
setoid_rewrite Entails_iff.
cbn.
intros.
rewrite LiftSpec_withSpace in H.
now apply H3.

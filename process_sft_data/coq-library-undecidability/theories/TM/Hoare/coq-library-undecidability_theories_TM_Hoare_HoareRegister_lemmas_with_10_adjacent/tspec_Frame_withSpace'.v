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

Lemma LiftTapes_Spec (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) P' (P : SpecV sig n) Q' (Q : F -> SpecV sig m) (pM : pTM sig^+ F m) : dupfree I -> Triple (tspec (P',Downlift P I)) pM (fun y => tspec (Q' y,Q y)) -> Triple (tspec (P',P)) (LiftTapes pM I) (fun y => tspec (Q' y,Frame P I (Q y))).
Proof.
unfold Frame.
rewrite !Triple_iff.
intros HDup HTrip.
eapply Realise_monotone.
{
apply LiftTapes_Realise.
assumption.
apply HTrip.
}
{
intros tin (yout, tout) (H&HInj).
cbn -[Downlift tspec] in *.
intros HP.
spec_assert H by now apply tape_fulfill_Downlift_select.
eapply tspecE in H as [H' H].
eapply tspecE in HP as [HP' HP].
eapply tspecI;cbn.
{
clear - H' HP'.
induction P';cbn in *.
all:firstorder.
}
clear H' HP'.
hnf.
intros j.
decide (Vector.In j I) as [HD|HD].
-
unfold Frame.
apply vect_nth_In' in HD as (ij&HD).
erewrite fill_correct_nth; eauto.
specialize (H ij).
now rewrite select_nth, HD in H.
-
unfold Frame.
rewrite fill_not_index; eauto.
specialize (HInj j HD).
rewrite HInj.
now apply HP.
Admitted.

Lemma LiftTapes_Spec_con (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) P' (P : SpecV sig n) Q' (Q : F -> SpecV sig m) R' (R : F -> SpecV sig n) (pM : pTM sig^+ F m) : dupfree I -> Triple (tspec (P',Downlift P I)) pM (fun y => tspec (Q' y,Q y)) -> (forall yout, Entails (tspec (Q' yout,Frame P I (Q yout))) (tspec (R' yout,R yout))) -> Triple (tspec (P',P)) (LiftTapes pM I) (fun y => tspec (R' y,R y)).
Proof.
intros ? ? <-%asPointwise.
eapply LiftTapes_Spec.
Admitted.

Lemma LiftTapes_SpecT (sig F : finType)(m n : nat) (I : Vector.t (Fin.t n) m) P' (P : SpecV sig n) (k : nat) Q' (Q : F -> SpecV sig m) (pM : pTM sig^+ F m) : dupfree I -> TripleT (tspec (P',Downlift P I)) k pM (fun y => tspec (Q' y,Q y)) -> TripleT (tspec (P',P)) k (LiftTapes pM I) (fun y => tspec (Q' y,Frame P I (Q y))).
Proof.
intros HDup (HTrip&HTrip').
split.
-
apply LiftTapes_Spec; eauto.
-
eapply TerminatesIn_monotone.
+
apply LiftTapes_Terminates; eauto.
+
intros tin k' (H&H').
split; auto.
Admitted.

Lemma LiftTapes_SpecT_con (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) P' (P : SpecV sig n) Q' (Q : F -> SpecV sig m) R' (R : F -> SpecV sig n) (k : nat) (pM : pTM sig^+ F m) : dupfree I -> TripleT (tspec (P',Downlift P I)) k pM (fun y => tspec (Q' y,Q y)) -> (forall yout, Entails (tspec (Q' yout,Frame P I (Q yout))) (tspec (R' yout,R yout))) -> TripleT (tspec (P',P)) k (LiftTapes pM I) (fun y => tspec (R' y,R y)).
Proof.
Admitted.

Lemma Downlift_withSpace (m n : nat) (sig : Type) (P : SpecV sig n) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n) : Downlift (withSpace P ss) I = withSpace (Downlift P I) (select I ss).
Proof.
unfold withSpace, Downlift.
eapply VectorSpec.eq_nth_iff; intros ? ? ->.
simpl_vector.
rewrite !select_nth.
simpl_vector.
Admitted.

Lemma tspec_Downlift_withSpace (m n : nat) (sig : Type) P' (P : SpecV sig n) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n): Entails ≃≃( P', Downlift (sig:=sig) (m:=m) (n:=n) (withSpace P ss) I) ≃≃( P',withSpace (Downlift P I) (select I ss)).
Proof.
rewrite Entails_iff.
intros H.
Admitted.

Lemma Triple_Downlift_withSpace (m n : nat) (sig : finType) P' (P : SpecV sig n) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n) (F : Type) (M : pTM sig^+ F m) (Q : F -> Assert sig^+ m) : Triple (tspec (P',withSpace (Downlift P I) (select I ss))) M Q -> Triple (tspec (P',Downlift (withSpace P ss) I)) M Q.
Proof.
Admitted.

Lemma TripleT_Downlift_withSpace (m n : nat) (sig : finType) P' (P : SpecV sig n) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n) (F : Type) (k : nat) (M : pTM sig^+ F m) (Q : F -> Assert sig^+ m) : TripleT (tspec (P',withSpace (Downlift P I) (select I ss))) k M Q -> TripleT (tspec (P',Downlift (withSpace P ss) I)) k M Q.
Proof.
Admitted.

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
Admitted.

Lemma Frame_withSpace (m n : nat) (sig : Type) (P : SpecV sig n) (P' : SpecV sig m) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n) (ss' : Vector.t nat m) : dupfree I -> Frame (withSpace P ss) I (withSpace P' ss') = withSpace (Frame P I P') (fill I ss ss').
Proof.
intros Hdup.
unfold Frame,withSpace.
eapply VectorSpec.eq_nth_iff; intros ? i ->.
simpl_vector.
decide (exists j, I[@j]=i) as [(j&Hj)|Hj].
+
erewrite !fill_correct_nth by eauto.
now simpl_vector.
+
assert (not_index I i).
{
hnf.
intros (k&<-) % vect_nth_In'.
contradict Hj.
eauto.
}
erewrite !fill_not_index by eauto.
Admitted.

Lemma LiftTapes_Spec_space (sig F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) P' (P : SpecV sig n) Q' (Q : F -> SpecV sig m) (pM : pTM sig^+ F m) (ss : Vector.t nat n) (ss' : Vector.t nat m) : dupfree I -> Triple (tspec (P',withSpace (Downlift P I) (select I ss))) pM (fun y => tspec (Q' y,withSpace (Q y) ss')) -> Triple (tspec (P',withSpace P ss)) (LiftTapes pM I) (fun y => tspec (Q' y,withSpace (Frame P I (Q y)) (fill I ss ss'))).
Proof.
intros H1 H2.
rewrite <- Downlift_withSpace in H2.
apply LiftTapes_Spec in H2.
setoid_rewrite tspec_Frame_withSpace' in H2.
Admitted.

Lemma LiftTapes_SpecT_space (sig F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) P' (P : SpecV sig n) (k : nat) Q' (Q : F -> SpecV sig m) (pM : pTM sig^+ F m) (ss : Vector.t nat n) (ss' : Vector.t nat m) : dupfree I -> TripleT (tspec (P',withSpace (Downlift P I) (select I ss))) k pM (fun y => tspec (Q' y,withSpace (Q y) ss')) -> TripleT (tspec (P',withSpace P ss)) k (LiftTapes pM I) (fun y => tspec (Q' y,withSpace (Frame P I (Q y)) (fill I ss ss'))).
Proof.
intros H1 H2.
rewrite <- Downlift_withSpace in H2.
apply LiftTapes_SpecT in H2.
setoid_rewrite tspec_Frame_withSpace' in H2.
Admitted.

Lemma LiftTapes_Spec_space_con (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) P' (P : SpecV sig n) Q' (Q : F -> SpecV sig m) R' (R : F -> SpecV sig n) (ss : Vector.t nat n) (ss' : Vector.t nat m) (ss'' : Vector.t nat n) (pM : pTM sig^+ F m) : dupfree I -> Triple (tspec (P',withSpace (Downlift P I) (select I ss))) pM (fun y => tspec (Q' y,withSpace (Q y) ss')) -> (forall yout, Entails (tspec (Q' yout,withSpace (Frame P I (Q yout)) (fill I ss ss'))) (tspec (R' yout,withSpace (R yout) ss''))) -> Triple (tspec (P',withSpace P ss)) (LiftTapes pM I) (fun y => tspec (R' y,withSpace (R y) ss'')).
Proof.
intros H1 H2 <-%asPointwise.
rewrite <- Downlift_withSpace in H2.
apply LiftTapes_Spec in H2.
setoid_rewrite tspec_Frame_withSpace' in H2.
Admitted.

Lemma LiftTapes_SpecT_space_con (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) P' (P : SpecV sig n) Q' (Q : F -> SpecV sig m) R' (R : F -> SpecV sig n) (ss : Vector.t nat n) (ss' : Vector.t nat m) (ss'' : Vector.t nat n) (k : nat) (pM : pTM sig^+ F m) : dupfree I -> TripleT (tspec (P',withSpace (Downlift P I) (select I ss))) k pM (fun y => tspec (Q' y,withSpace (Q y) ss')) -> (forall yout, Entails (tspec (Q' yout,withSpace (Frame P I (Q yout)) (fill I ss ss'))) (tspec (R' yout,withSpace (R yout) ss''))) -> TripleT (tspec (P',withSpace P ss)) k (LiftTapes pM I) (fun y => tspec (R' y,withSpace (R y) ss'')).
Proof.
intros H1 H2 <-%asPointwise.
rewrite <- Downlift_withSpace in H2.
apply LiftTapes_SpecT in H2.
setoid_rewrite tspec_Frame_withSpace' in H2.
Admitted.

Lemma LiftSpec_surjectTape_tspec_single t T : tspec_single (LiftSpec_single T) t -> tspec_single T (surjectTape Retr_g (inl UNKNOWN) t).
Proof.
Admitted.

Lemma LiftSpec_surjectTape_tspec_single' t T : tspec_single T (surjectTape Retr_g (inl UNKNOWN) t) -> tspec_single (LiftSpec_single T) t.
Proof.
Admitted.

Lemma LiftSpec_surjectTapes_tspec tin P' P : tin ≃≃ (P', LiftSpec P) -> surjectTapes Retr_g (inl UNKNOWN) tin ≃≃ (P',P).
Proof.
intros (H'&H)%tspecE.
eapply tspecI.
easy.
intros i; specialize (H i); cbn.
unfold LiftSpec in *.
simpl_tape in *.
Admitted.

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

Lemma tspec_Frame_withSpace' (m n : nat) (I : Vector.t (Fin.t n) m): dupfree I -> forall (sig : Type) Q (P : SpecV sig n) (P' : SpecV sig m) (ss : Vector.t nat n) (ss' : Vector.t nat m), Entails ≃≃( Q , Frame (withSpace P ss) I (withSpace P' ss')) ≃≃( Q, withSpace (Frame P I P') (fill I ss ss')).
Proof.
intros H1 **.
erewrite <- Frame_withSpace; eauto.

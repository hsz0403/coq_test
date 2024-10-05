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

Lemma tspec_single_Contains_size_Contains {sigX X : Type} {cX : codable sigX X} (r : Retract sigX sig) (x : X) (s : nat) (t : tape sig^+) : tspec_single (Contains_size r x s) t -> tspec_single (Contains r x) t.
Proof.
cbn.
Admitted.

Lemma tspecE {n : nat} Ps Pv t: tspec (n:=n) (Ps,Pv) t -> (List.fold_right and True Ps /\ forall (i : Fin.t n), tspec_single Pv[@i] t[@i]).
Proof.
cbn.
induction Ps;cbn in *.
easy.
intros [].
specialize (IHPs H0) as [H' ?].
split.
Admitted.

Lemma tspecI {n : nat} P t: (List.fold_right and True (fst P)) -> (forall (i : Fin.t n), tspec_single (snd P)[@i] t[@i]) -> tspec (n:=n) P t.
Proof.
destruct P as (Ps&P).
induction Ps;cbn in *.
easy.
intros H' ?.
split.
now eapply H';left.
eapply IHPs.
Admitted.

Lemma tspec_iff {n : nat} Ps Pv t: tspec (n:=n) (Ps,Pv) t <-> (List.fold_right and True Ps /\ forall (i : Fin.t n), tspec_single Pv[@i] t[@i]).
Proof.
split.
eapply tspecE;eauto.
intros [].
Admitted.

Lemma tspec_Entails {n : nat} Ps Pv: Entails (tspec (n:=n) (Ps,Pv)) (fun t => List.fold_right and True Ps /\ forall (i : Fin.t n), tspec_single Pv[@i] t[@i]).
Proof.
apply EntailsI.
Admitted.

Lemma tspec_single_withSpace_tspec_single (P : RegSpec) (size : nat) t : tspec_single (withSpace_single P size) t -> tspec_single P t.
Proof.
intros.
Admitted.

Lemma tspec_withSpace_tspec {n : nat} Q P (s : Vector.t nat n) t : tspec (Q,withSpace P s) t -> tspec (Q,P) t.
Proof.
unfold withSpace.
intros [HP H]%tspecE.
apply tspecI.
easy.
intros i; specialize (H i).
simpl_vector in *.
Admitted.

Lemma tspec_single_tspec_single_withSpace (P : RegSpec) t : tspec_single P t -> tspec_single (withSpace_single P (dummy_size t P)) t.
Proof.
intros H.
Admitted.

Lemma tspec_tspec_withSpace (n : nat) Q (P : SpecV n) t : tspec (Q,P) t -> tspec (Q,withSpace P (dummy_sizes t P)) t.
Proof.
unfold withSpace, dummy_sizes in *.
intros [HP ?]%tspecE.
eapply tspecI.
cbn in *; auto.
intros i; specialize (H i); cbn in *.
simpl_vector.
Admitted.

Instance fold_right_iff : Proper (Forall2 iff ==> iff ==> iff) (implList).
Proof.
intros xs;induction xs;cbn;intros ? H';inv H';cbn.
easy.
Admitted.

Lemma implList_iff P (Ps : list Prop): implList Ps P <-> (List.fold_right and True Ps -> P).
Proof.
induction Ps in P|-*;cbn.
firstorder.
setoid_rewrite IHPs.
Admitted.

Lemma implListE P (Ps : list Prop): implList Ps P -> (List.fold_right and True Ps -> P).
Proof.
Admitted.

Lemma implListI (P:Prop) (Ps : list Prop): (List.fold_right and True Ps -> P) -> implList Ps P.
Proof.
Admitted.

Instance Forall2_refl X (R: X -> _): Reflexive R -> Reflexive (Forall2 R).
Proof.
Admitted.

Lemma tspec_introPure (sig: finType) (n : nat) P (Ps : SpecV sig n) Q: implList P (Entails (≃≃([],Ps)) Q) -> Entails (tspec (P,Ps)) Q.
Proof.
setoid_rewrite Entails_iff.
rewrite implList_iff.
intros H ? []%tspecE.
eapply H.
eassumption.
Admitted.

Lemma tspec_revertPure (sig: finType) (n : nat) (P0:Prop) P (Ps : SpecV sig n) Q: P0 -> Entails (tspec (P0::P,Ps)) Q -> Entails (tspec (P,Ps)) Q.
Proof.
setoid_rewrite Entails_iff.
unfold tspec;cbn.
Admitted.

Lemma Triple_introPure (F sig: finType) (n : nat) P (Ps : SpecV sig n) Q (pM : pTM sig^+ F n) : implList P (Triple (≃≃([],Ps)) pM Q) -> Triple (tspec (P,Ps)) pM Q.
Proof.
intros.
rewrite tspec_Entails.
apply Triple_and_pre.
cbn in H.
Admitted.

Lemma TripleT_introPure (sig F : finType) (n : nat) P (Ps : SpecV sig n) Q k (pM : pTM sig^+ F n) : implList P (TripleT (≃≃([],Ps)) k pM Q) -> TripleT (tspec (P,Ps)) k pM Q.
Proof.
intros.
rewrite tspec_Entails.
apply TripleT_and_pre.
cbn in H.
Admitted.

Lemma Triple_RemoveSpace_ex (n : nat) (sig : finType) (F : Type) X (P : SpecV sig n) P' (M : pTM sig^+ F n) Q Q' Ctx (fs : _ -> Vector.t (nat->nat) n) : (forall s, Triple (tspec (P',withSpace P s)) M (fun y t => exists x:X, Ctx x (tspec (Q' x y,withSpace (Q x y) (appSize (fs x) s)) t))) -> (* Specifications with size will always have this form *) (forall x, Proper (Basics.impl ==> Basics.impl) (Ctx x)) -> Triple (tspec (P',P)) M (fun y t => exists x, Ctx x (tspec (Q' x y ,Q x y) t)).
Proof.
intros HTrip Hctx.
setoid_rewrite Triple_iff in HTrip.
rewrite Triple_iff.
eapply Realise_monotone with (R' := fun tin '(yout, tout) => forall s, tspec (P',withSpace P s) tin -> exists x:X, Ctx x (tspec (Q' x yout,withSpace (Q x yout) (appSize (fs x) s)) tout)).
-
unfold Triple_Rel, Realise in *.
intros tin k outc HLoop.
intros s HP.
specialize HTrip with (1 := HLoop) (2 := HP) as [x H''].
eexists.
eauto.
-
clear HTrip.
intros tin (yout, tout).
intros H HP.
specialize (H (dummy_sizes tin P)).
spec_assert H by now apply tspec_tspec_withSpace.
destruct H as (x&H).
exists x.
eapply Hctx.
2:eassumption.
intro H'.
Admitted.

Instance fold_right_impl' : Proper (Forall2 Basics.impl --> Basics.impl ==> Basics.impl) (implList).
Proof.
intros xs;induction xs;cbn;intros ? H';inv H';cbn.
easy.
firstorder.

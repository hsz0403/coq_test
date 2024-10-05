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

Lemma LiftTapes_Spec_con (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) P' (P : SpecV sig n) Q' (Q : F -> SpecV sig m) R' (R : F -> SpecV sig n) (pM : pTM sig^+ F m) : dupfree I -> Triple (tspec (P',Downlift P I)) pM (fun y => tspec (Q' y,Q y)) -> (forall yout, Entails (tspec (Q' yout,Frame P I (Q yout))) (tspec (R' yout,R yout))) -> Triple (tspec (P',P)) (LiftTapes pM I) (fun y => tspec (R' y,R y)).
Proof.
intros ? ? <-%asPointwise.
eapply LiftTapes_Spec.
all:easy.

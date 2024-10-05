From Coq Require Import FunInd.
From Undecidability Require Import TM.Code.CodeTM.
From Undecidability.TM.Compound Require Export CopySymbols MoveToSymbol.
From Undecidability Require Import TM.Basic.Mono.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac TM.Compound.Multi.
From Undecidability Require Import TM.Lifting.LiftAlphabet.
Local Generalizable All Variables.
Set Default Proof Using "Type".
Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Section Copy.
Variable sig : finType.
Variable stop : sig -> bool.
Variable f : sig -> sig.
End Copy.
Section Move.
Variable (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig).
Definition isStop (s: sig^+) := match s with inl STOP => true | _ => false end.
Definition isStart (s: sig^+) := match s with inl START => true | _ => false end.
Definition MoveRight := Return (MoveToSymbol isStop id) tt.
Definition MoveLeft := Return (MoveToSymbol_L isStart id) tt.
Definition Reset := MoveRight.
Definition MoveRight_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) := ignoreParam (fun tin tout => forall (x : X) (s : nat), tin[@Fin0] ≃(;s) x -> tout[@Fin0] ≂(;s) x).
Definition MoveLeft_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) := ignoreParam (fun tin tout => forall (x : X) (s : nat), tin[@Fin0] ≂(;s) x -> tout[@Fin0] ≃(;s) x).
Definition Reset_size {sigX : Type} {cX : codable sigX X} (x : X) (s : nat) := S (size x + s).
Definition Reset_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) := ignoreParam (fun tin tout => forall (s : nat) (x:X), tin[@Fin0] ≃(;s) x -> isVoid_size tout[@Fin0] (Reset_size x s)).
Definition MoveRight_steps {sigX : Type} (cX : codable sigX X) (x : X) := 8 + 4 *size x.
Definition MoveLeft_steps {sigX : Type} {cX : codable sigX X} (x:X) := 8 + 4 *size x.
Definition Reset_steps {sigX : Type} {cX : codable sigX X} (x:X) := 8 + 4 *size x.
Definition Reset_Terminates : projT1 Reset ↓ (fun tin k => exists x, tin[@Fin0] ≃ x /\ Reset_steps x <= k).
Proof.
exact MoveRight_Terminates.
Definition ResetEmpty : pTM sig^+ unit 1 := Move Rmove.
Definition ResetEmpty_size : nat -> nat := S.
Definition ResetEmpty_Rel : pRel sig^+ unit 1 := ignoreParam ( fun tin tout => forall (s : nat) (x : X), tin[@Fin0] ≃(;s) x -> cX x = nil -> isVoid_size tout[@Fin0] (ResetEmpty_size s) ).
Definition ResetEmpty_steps := 1.
Definition ResetEmpty1 : pTM sig^+ (FinType(EqType unit)) 1 := Move Rmove;; Move Rmove.
Definition ResetEmpty1_size : nat -> nat := S >> S.
Definition ResetEmpty1_Rel : pRel sig^+ (FinType(EqType unit)) 1 := ignoreParam ( fun tin tout => forall (x : X) (s : nat), tin[@Fin0] ≃(;s) x -> size x = 1 -> isVoid_size tout[@Fin0] (ResetEmpty1_size s)).
Definition ResetEmpty1_steps := 3.
End Move.
Arguments Reset_size {X sigX cX} : simpl never.
Arguments Reset_steps {X sigX cX} : simpl never.
Typeclasses Opaque Reset_size.
Typeclasses Opaque Reset_steps.
Section CopyValue.
Variable (sig: finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig).
Definition CopyValue := LiftTapes (MoveRight _) [|Fin0|];; CopySymbols_L (@isStart sig).
Definition CopyValue_size {sig: Type} {cX : codable sig X} (x : X) (s1 : nat) := s1 - S (size x).
Definition CopyValue_Rel : Rel (tapes (sig^+) 2) (unit * tapes (sig^+) 2) := ignoreParam ( fun tin tout => forall (x:X) (sx s1 : nat), tin[@Fin0] ≃(;sx) x -> isVoid_size tin[@Fin1] s1 -> tout[@Fin0] ≃(;sx) x /\ tout[@Fin1] ≃(;CopyValue_size x s1) x ).
Definition CopyValue_steps {sig:Type} {cX : codable sig X} (x:X) := 25 + 12 *size x.
End CopyValue.
Arguments CopyValue_size {X sig cX} : simpl never.
Arguments CopyValue_steps {X sig cX} : simpl never.
Typeclasses Opaque CopyValue_size.
Typeclasses Opaque CopyValue_steps.
Section MoveValue.
Variable sig : finType.
Variable (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig).
Definition MoveValue : pTM sig^+ unit 2 := LiftTapes (Reset _) [|Fin1|];; CopyValue _;; LiftTapes (Reset _) [|Fin0|].
Definition MoveValue_size_x {sigX : Type} {cX : codable sigX X} (x : X) (sx : nat) := S (size x + sx).
Definition MoveValue_size_y {sigX sigY : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (y : Y) (sy : nat) := sy + size cY y -size x.
Definition MoveValue_Rel : pRel sig^+ unit 2 := ignoreParam ( fun tin tout => forall (x : X) (y : Y) (sx sy : nat), tin[@Fin0] ≃(;sx) x -> tin[@Fin1] ≃(;sy) y -> isVoid_size tout[@Fin0] (MoveValue_size_x x sx) /\ tout[@Fin1] ≃(;MoveValue_size_y x y sy) x).
Definition MoveValue_steps {sigX sigY:Type} {cX : codable sigX X} {cY : codable sigY Y} (x:X) (y:Y) := 43 + 16 *size x + 4 * size cY y.
End MoveValue.
Arguments MoveValue_size_x {X sigX cX} : simpl never.
Arguments MoveValue_size_y {X Y sigX sigY cX cY} : simpl never.
Arguments MoveValue_steps {X Y sigX sigY cX cY} : simpl never.
Typeclasses Opaque MoveValue_size_x MoveValue_size_y.
Typeclasses Opaque MoveValue_steps.
Section Translate.
Variable (sig : finType).
Variable (sigX X : Type) (cX : codable sigX X).
Variable (I1 I2 : Retract sigX sig).
Definition translate : sig^+ -> sig^+ := fun t => match t with | inl _ => t | inr x => match Retr_g (Retract := I1) x with | Some y => inr (Retr_f (Retract := I2) y) | None => inl UNKNOWN end end.
Definition Translate' := MoveToSymbol (@isStop sig) translate.
Definition Translate'_Rel : pRel sig^+ unit 1 := ignoreParam ( fun tin tout => forall (x : X) (s : nat), tin[@Fin0] ≃(I1; s) x -> tout[@Fin0] ≂(I2; s) x ).
Definition Translate'_steps {sigX X : Type} {cX : codable sigX X} (x:X) := 8 + 4 *size x.
Definition Translate := Translate';; MoveLeft _.
Definition Translate_Rel : pRel sig^+ unit 1 := ignoreParam ( fun tin tout => forall (x : X) (s : nat), tin[@Fin0] ≃(I1; s) x -> tout[@Fin0] ≃(I2; s) x ).
Definition Translate_steps {sigX:Type} {cX : codable sigX X} (x : X) := 17 + 8 *size x.
Definition Translate_T : tRel sig^+ 1 := fun tin k => exists x, tin[@Fin0] ≃(I1) x /\ Translate_steps x <= k.
End Translate.
Arguments Translate_steps {X sigX cX}.
Ltac smpl_TM_Copy := once lazymatch goal with | [ |- Translate _ _ ⊨ _] => notypeclasses refine (@Translate_Realise _ _ _ _ _ _);shelve | [ |- projT1 (Translate _ _) ↓ _] => notypeclasses refine (@Translate_Terminates _ _ _ _ _ _);shelve | [ |- Reset _ ⊨ _] => notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve | [ |- projT1 (Reset _) ↓ _] => notypeclasses refine (@Reset_Terminates _ _ _ _ _);shelve | [ |- CopyValue _ ⊨ _] => notypeclasses refine (@CopyValue_Realise _ _ _ _ _);shelve | [ |- projT1 (CopyValue _) ↓ _] => notypeclasses refine (@CopyValue_Terminates _ _ _ _ _);shelve | [ |- MoveValue _ ⊨ _] => notypeclasses refine (@MoveValue_Realise _ _ _ _ _ _ _ _ _);shelve | [ |- projT1 (MoveValue _) ↓ _] => notypeclasses refine (@MoveValue_Terminates _ _ _ _ _ _ _ _ _);shelve end.
Smpl Add smpl_TM_Copy : TM_Correct.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister HoareTactics.
Definition CopyValue_sizefun {sigX X : Type} {cX : codable sigX X} (x : X) : Vector.t (nat->nat) 2 := [|id; CopyValue_size x|].
Definition MoveValue_size {X Y sigX sigY : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (y : Y) : Vector.t (nat->nat) 2 := [|MoveValue_size_x x; MoveValue_size_y x y|].
Ltac hstep_Reset := lazymatch goal with | [ |- TripleT ?P ?k (CopyValue _) ?Q ] => notypeclasses refine (CopyValue_SpecT_size _ _ _ _) | [ |- TripleT ?P ?k (Reset _) ?Q ] => eapply @Reset_SpecT_space | [ |- TripleT ?P ?k (ResetEmpty _) ?Q ] => eapply @ResetEmpty_SpecT_space | [ |- TripleT ?P ?k (ResetEmpty1 _) ?Q ] => eapply @ResetEmpty1_SpecT_space | [ |- TripleT ?P ?k (MoveValue _) ?Q ] => eapply @MoveValue_SpecT_size | [ |- TripleT ?P ?k (Translate _ _) ?Q ] => eapply @Translate_SpecT_size end.
Smpl Add hstep_Reset : hstep_Spec.

Lemma Reset_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) : TripleT (≃≃([], [|Contains _ x|])) (Reset_steps x) (Reset sig) (fun _ => ≃≃([], [|Void|])).
Proof.
eapply TripleT_RemoveSpace.
Admitted.

Lemma Reset_Spec_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) ss : Triple (≃≃(([], withSpace [|Contains _ x |] ss))) (Reset sig) (fun _ => ≃≃(([], withSpace [|Void|] (appSize [|Reset_size x|] ss)))).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma Reset_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) : Triple (≃≃([], [|Contains _ x|])) (Reset sig) (fun _ => ≃≃([], [|Void|])).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma ResetEmpty_SpecT_space (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 1) : cX x = [] -> TripleT (≃≃(([], withSpace [|Contains _ x |] ss))) (ResetEmpty_steps) (ResetEmpty sig) (fun _ => ≃≃(([], withSpace [|Void|] (appSize [|ResetEmpty_size|] ss)))).
Proof.
intros HEncEmpty.
eapply RealiseIn_TripleT.
-
eapply ResetEmpty_Sem.
-
intros tin [] tout H HEnc.
unfold withSpace in *.
cbn in *.
specialize (HEnc Fin0); cbn in *.
simpl_vector in *; cbn in *.
modpon H.
Admitted.

Lemma ResetEmpty_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) : cX x = [] -> TripleT (≃≃([], [|Contains _ x|])) (ResetEmpty_steps) (ResetEmpty sig) (fun _ => ≃≃([], [|Void|])).
Proof.
intros.
eapply TripleT_RemoveSpace.
intros.
Admitted.

Lemma ResetEmpty_Spec_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) ss : cX x = [] -> Triple (≃≃(([], withSpace [|Contains _ x |] ss))) (ResetEmpty sig) (fun _ => ≃≃(([], withSpace [|Void|] (appSize [|ResetEmpty_size|] ss)))).
Proof.
intros.
eapply TripleT_Triple.
Admitted.

Lemma ResetEmpty_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) : cX x = [] -> Triple (≃≃([], [|Contains _ x|])) (ResetEmpty sig) (fun _ => ≃≃([], [|Void|])).
Proof.
intros.
eapply TripleT_Triple.
Admitted.

Lemma ResetEmpty1_SpecT_space (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 1) : size x = 1 -> TripleT (≃≃(([], withSpace [|Contains _ x |] ss))) (ResetEmpty1_steps) (ResetEmpty1 sig) (fun _ => ≃≃(([], withSpace [|Void|] (appSize [|ResetEmpty1_size|] ss)))).
Proof.
intros HEncEmpty.
eapply RealiseIn_TripleT.
-
eapply ResetEmpty1_Sem.
-
intros tin [] tout H HEnc.
cbn in *.
unfold withSpace in *.
specialize (HEnc Fin0); cbn in *.
simpl_vector in *; cbn in *.
modpon H.
Admitted.

Lemma ResetEmpty1_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) : size x = 1 -> TripleT (≃≃([], [|Contains _ x|])) (ResetEmpty1_steps) (ResetEmpty1 sig) (fun _ => ≃≃([], [|Void|])).
Proof.
intros.
eapply TripleT_RemoveSpace.
intros.
Admitted.

Lemma ResetEmpty1_Spec_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) ss : size x = 1 -> Triple (≃≃(([], withSpace [|Contains _ x |] ss))) (ResetEmpty1 sig) (fun _ => ≃≃(([], withSpace [|Void|] (appSize [|ResetEmpty1_size|] ss)))).
Proof.
intros.
eapply TripleT_Triple.
Admitted.

Lemma MoveValue_SpecT_size (sig : finType) (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) (ss : Vector.t nat 2) : TripleT (≃≃(([], withSpace [|Contains _ x; Contains _ y |] ss))) (MoveValue_steps x y) (MoveValue sig) (fun _ => ≃≃(([], withSpace [|Void; Contains _ x|] (appSize (MoveValue_size x y) ss)))).
Proof.
unfold withSpace.
eapply Realise_TripleT.
-
apply MoveValue_Realise with (X := X) (Y := Y).
-
apply MoveValue_Terminates with (X := X) (Y := Y).
-
intros tin [] tout H HEnc.
cbn in *.
specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
simpl_vector in *; cbn in *.
modpon H.
tspec_solve.
-
intros tin k HEnc.
cbn in *.
specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
simpl_vector in *; cbn in *.
Admitted.

Lemma MoveValue_SpecT (sig : finType) (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) : TripleT (≃≃([], [|Contains _ x; Contains _ y|])) (MoveValue_steps x y) (MoveValue sig) (fun _ => ≃≃([], [|Void; Contains _ x|])).
Proof.
eapply TripleT_RemoveSpace.
Admitted.

Lemma MoveValue_Spec_size (sig : finType) (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) (ss : Vector.t nat 2) : Triple (≃≃(([], withSpace [|Contains _ x; Contains _ y |] ss))) (MoveValue sig) (fun _ => ≃≃(([], withSpace [|Void; Contains _ x|] (appSize (MoveValue_size x y) ss)))).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma MoveValue_Spec (sig : finType) (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) : Triple (≃≃([], [|Contains _ x; Contains _ y|])) (MoveValue sig) (fun _ => ≃≃([], [|Void; Contains _ x|])).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma Translate_SpecT_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I1 I2 : Retract sigX sig) (x : X) (ss : Vector.t nat 1) : TripleT (≃≃(([], withSpace [|Contains I1 x |] ss))) (Translate_steps x) (Translate I1 I2) (fun _ => ≃≃(([], withSpace [|Contains I2 x|] (appSize [|id|] ss)))).
Proof.
unfold withSpace.
eapply Realise_TripleT.
-
apply Translate_Realise with (X := X).
-
apply Translate_Terminates with (X := X).
-
intros tin [] tout H HEnc.
cbn in *.
specialize (HEnc Fin0) as HEnc0; simpl_vector in *; cbn in *.
modpon H.
tspec_solve.
-
intros tin k HEnc Hk.
cbn in *.
specialize (HEnc Fin0) as HEnc0.
simpl_vector in *; cbn in *.
unfold Translate_T.
Admitted.

Lemma Translate_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I1 I2 : Retract sigX sig) (x : X) : TripleT (≃≃([], [|Contains I1 x|])) (Translate_steps x) (Translate I1 I2) (fun _ => ≃≃([], [|Contains I2 x|])).
Proof.
eapply TripleT_RemoveSpace.
Admitted.

Lemma Translate_Spec_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I1 I2 : Retract sigX sig) (x : X) (ss : Vector.t nat 1) : Triple (≃≃(([], withSpace [|Contains I1 x |] ss))) (Translate I1 I2) (fun _ => ≃≃(([], withSpace [|Contains I2 x|] (appSize [|id|] ss)))).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma Translate_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I1 I2 : Retract sigX sig) (x : X) : Triple (≃≃([], [|Contains I1 x|])) (Translate I1 I2) (fun _ => ≃≃([], [|Contains I2 x|])).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma ResetEmpty1_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) : size x = 1 -> Triple (≃≃([], [|Contains _ x|])) (ResetEmpty1 sig) (fun _ => ≃≃([], [|Void|])).
Proof.
intros.
eapply TripleT_Triple.
now apply ResetEmpty1_SpecT.

From Undecidability Require Import CodeTM.
From Undecidability Require Import Basic.Mono.
From Undecidability Require Import TM.Compound.WriteString.
From Undecidability Require Import TMTac.
Arguments WriteString_Fun : simpl never.
Section WriteValue.
Variable (sig: finType) (X: Type) (cX: codable sig X).
Definition WriteValue (x : X) : pTM sig^+ unit 1 := WriteString Lmove (rev (inl START :: map inr (encode x) ++ [inl STOP])).
Definition WriteValue_size (sig:Type) (cX: codable sig X) (x : X) (s : nat) : nat := s - (S (size x)).
Definition WriteValue_Rel (x:X) : Rel (tapes sig^+ 1) (unit * tapes sig^+ 1) := fun tin '(_, tout) => forall (s0:nat), isVoid_size tin[@Fin0] s0 -> tout[@Fin0] ≃(;WriteValue_size cX x s0) x.
Definition WriteValue_steps (l : nat) := 3 + 2 * l.
End WriteValue.
Arguments WriteValue_size {X sig cX}.
Arguments WriteValue [sig X cX].
Ltac smpl_TM_WriteValue := once lazymatch goal with | [ |- WriteValue _ ⊨ _ ] => eapply RealiseIn_Realise; apply WriteValue_Sem | [ |- WriteValue _ ⊨c(_) _ ] => apply WriteValue_Sem | [ |- projT1 (WriteValue _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply WriteValue_Sem end.
Smpl Add smpl_TM_WriteValue : TM_Correct.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister HoareTactics.
Section WriteValue.
Variable (sig: finType) (X: Type) (cX: codable sig X).
Definition WriteValue_sizefun (x : X) : Vector.t (nat->nat) 1 := [| WriteValue_size x |].
End WriteValue.
Ltac hstep_WriteValue := match goal with | [ |- TripleT ?P ?k (WriteValue _) ?Q ] => eapply WriteValue_SpecT_size end.
Smpl Add hstep_WriteValue : hstep_Spec.

Lemma WriteValue_SpecT_size (x : X) (ss : Vector.t nat 1) : TripleT (≃≃(([], withSpace [|Void |] ss))) (WriteValue_steps (size x)) (WriteValue x) (fun _ => ≃≃(([], withSpace [|Contains _ x|] (appSize (WriteValue_sizefun x) ss)))).
Proof.
unfold withSpace.
eapply RealiseIn_TripleT.
-
apply WriteValue_Sem.
-
intros tin yout tout H HEnc.
cbn in *.
specialize (HEnc Fin0).
simpl_vector in *; cbn in *.
tspec_solve.
now apply H.

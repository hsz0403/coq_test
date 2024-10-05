From Undecidability.TM Require Import ProgrammingTools.
Set Default Proof Using "Type".
Local Arguments skipn { A } !n !l.
Section CasePair.
Variable (sigX sigY: finType) (X Y: Type) (cX: codable sigX X) (cY: codable sigY Y).
Local Notation sigPair := (sigPair sigX sigY).
Definition stopAfterFirst : sigPair^+ -> bool := fun x => match x with | inr (sigPair_Y y) => true | inl STOP => true | _ => false end.
Definition stopAtStart : sigPair^+ -> bool := fun x => match x with | inl START => true | _ => false end.
Definition CasePair_size0 {sigX X : Type} {cX : codable sigX X} (x : X) (s0 : nat) := s0 + size x.
Definition CasePair_size1 {sigX X : Type} {cX : codable sigX X} (x : X) (s1 : nat) := s1 - (size x) - 1.
Definition CasePair_Rel : pRel sigPair^+ unit 2 := ignoreParam ( fun tin tout => forall (p : X * Y) (s0 s1 : nat), tin[@Fin0] ≃(;s0) p -> isVoid_size tin[@Fin1] s1 -> tout[@Fin0] ≃(;CasePair_size0 (fst p) s0) snd p /\ tout[@Fin1] ≃(;CasePair_size1 (fst p) s1) fst p ).
Definition CasePair : pTM sigPair^+ unit 2 := LiftTapes (WriteMove (inl STOP) Lmove) [|Fin1|];; LiftTapes (MoveToSymbol stopAfterFirst id;; Move Lmove) [|Fin0|];; CopySymbols_L stopAtStart;; LiftTapes (MoveToSymbol stopAfterFirst id;; Move Lmove;; Write (inl START)) [|Fin0|].
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Local Arguments size : simpl never.
Definition CasePair_steps {sigX X : Type} {cX : codable sigX X} (x : X) := 34 + 16 * size x.
Definition CasePair_T : tRel sigPair^+ 2 := fun tin k => exists (p : X * Y), tin[@Fin0] ≃ p /\ CasePair_steps (fst p) <= k.
Definition Constr_pair_size {sigX X : Type} {cX : codable sigX X} (x : X) (s1 : nat) := s1 - size x.
Definition Constr_pair_Rel : pRel sigPair^+ unit 2 := ignoreParam ( fun tin tout => forall (x : X) (y : Y) (s0 s1 : nat), tin[@Fin0] ≃(;s0) x -> tin[@Fin1] ≃(;s1) y -> tout[@Fin0] ≃(;s0) x /\ tout[@Fin1] ≃(;Constr_pair_size x s1) (x, y) ).
Definition Constr_pair : pTM sigPair^+ unit 2 := LiftTapes (MoveRight _;; Move Lmove) [|Fin0|];; CopySymbols_L stopAtStart.
Definition Constr_pair_steps {sigX X : Type} {cX : codable sigX X} (x : X) : nat := 19 + 12 * size x.
Definition Constr_pair_T : tRel sigPair^+ 2 := fun tin k => exists (x : X), tin[@Fin0] ≃ x /\ Constr_pair_steps x <= k.
Definition Snd_size {sigX X : Type} {cX : codable sigX X} (x : X) (s : nat) := s + size x.
Definition Snd_Rel : pRel sigPair^+ unit 1 := ignoreParam (fun tin tout => forall (p : X*Y) (s : nat), tin[@Fin0] ≃(;s) p -> tout[@Fin0] ≃(; Snd_size (fst p) s) snd p).
Definition Snd : pTM sigPair^+ unit 1 := MoveToSymbol stopAfterFirst id;; Move Lmove;; Write (inl START).
Definition Snd_steps {sigX X : Type} {cX : codable sigX X} (x : X) := 12 + 4 * size x.
Definition Snd_T : tRel sigPair^+ 1 := fun tin k => exists p : X*Y, tin[@Fin0] ≃ p /\ Snd_steps (fst p) <= k.
Goal forall (x : X) (s : nat), Constr_pair_size x (CasePair_size0 x s) = s.
Proof.
intros.
unfold Constr_pair_size, CasePair_size0.
lia.
End CasePair.
Arguments Constr_pair_size {sigX X cX} : simpl never.
Arguments CasePair_size0 {sigX X cX} : simpl never.
Arguments CasePair_size1 {sigX X cX} : simpl never.
Arguments Constr_pair_steps {sigX X cX} : simpl never.
Arguments CasePair_steps {sigX X cX} : simpl never.
Arguments CasePair_steps {sigX X cX} : simpl never.
Ltac smpl_TM_CasePair := once lazymatch goal with | [ |- CasePair _ _ ⊨ _ ] => apply CasePair_Realise | [ |- projT1 (CasePair _ _) ↓ _ ] => apply CasePair_Terminates | [ |- Constr_pair _ _ ⊨ _ ] => apply Constr_pair_Realise | [ |- projT1 (Constr_pair _ _) ↓ _] => apply Constr_pair_Terminates | [ |- Snd _ _ ⊨ _ ] => apply Snd_Realise | [ |- projT1 (Snd _ _) ↓ _] => apply Snd_Terminates end.
Smpl Add smpl_TM_CasePair : TM_Correct.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister HoareTactics.
Section CasePair.
Variable (X Y : Type) (sigX sigY : finType) (codX : codable sigX X) (codY : codable sigY Y).
Definition Constr_pair_sizefun (x : X) : Vector.t (nat->nat) 2 := [|id; Constr_pair_size x|].
Definition CasePair_size (p : X*Y) : Vector.t (nat->nat) 2 := [| CasePair_size0 (fst p); CasePair_size1 (fst p) |].
End CasePair.
Ltac hstep_Pair := match goal with | [ |- TripleT ?P ?k (Constr_pair _ _) ?Q ] => eapply (Constr_pair_SpecT_size _ _ _ _) | [ |- TripleT ?P ?k (CasePair _ _) ?Q ] => eapply (CasePair_SpecT_size _ _ _) end.
Smpl Add hstep_Pair : hstep_Spec.

Lemma Constr_pair_Realise : Constr_pair ⊨ Constr_pair_Rel.
Proof.
eapply Realise_monotone.
{
unfold Constr_pair.
TM_Correct.
-
apply MoveRight_Realise with (X := X).
}
{
intros tin ((), tout) H.
intros x y s0 s1 HEncX HEncY.
TMSimp; clear_trivial_eqs.
rename H into HMoveRight; rename H0 into HCopy.
modpon HMoveRight.
destruct HMoveRight as (ls&HMoveRight&Hs); TMSimp.
rewrite CopySymbols_L_correct_moveleft in HCopy; cbn in *; auto.
-
apply pair_eq in HCopy as (HCopy1&HCopy2).
TMSimp.
split.
+
repeat econstructor.
cbn.
f_equal.
now rewrite map_rev, rev_involutive.
lia.
+
repeat econstructor.
cbn.
f_equal.
simpl_tape.
destruct HEncY as (ls'&HEncY&Hs'); TMSimp_goal.
rewrite map_map, map_rev, rev_involutive.
cbn.
*
now rewrite !map_map, map_app, <- app_assoc, !map_map.
*
simpl_list.
rewrite skipn_length.
unfold Constr_pair_size.
destruct HEncY as (ls'&HEncY&Hs').
TMSimp.
unfold size.
lia.
-
rewrite map_rev, List.map_map.
now intros ? (?&<-&?) % in_rev % in_map_iff.
}

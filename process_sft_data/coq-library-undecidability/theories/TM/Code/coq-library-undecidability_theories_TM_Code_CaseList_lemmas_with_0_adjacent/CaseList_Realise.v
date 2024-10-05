From Undecidability.TM Require Import ProgrammingTools.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Set Default Proof Using "Type".
Section CaseList.
Variable X : Type.
Variable (sigX : finType).
Hypothesis (cX : codable sigX X).
Set Default Proof Using "Type".
Definition stop (s: (sigList sigX)^+) := match s with | inr (sigList_cons) => true | inr (sigList_nil) => true | inl _ => true | _ => false end.
Definition Skip_cons : pTM (sigList sigX)^+ unit 1 := Move Rmove;; MoveToSymbol stop id.
Definition M1 : pTM (sigList sigX)^+ unit 2 := LiftTapes Skip_cons [|Fin0|];; LiftTapes (Write (inl STOP)) [|Fin1|];; MovePar Lmove Lmove;; CopySymbols_L stop;; LiftTapes (Write (inl START)) [|Fin1|].
Definition CaseList : pTM (sigList sigX)^+ bool 2 := LiftTapes (Move Rmove) [|Fin0|];; Switch (LiftTapes (ReadChar) [|Fin0|]) (fun s => match s with | Some (inr sigList_nil) => (* nil *) Return (LiftTapes (Move Lmove) [|Fin0|]) false | Some (inr sigList_cons) => (* cons *) M1;; LiftTapes Skip_cons [|Fin0|];; Return (LiftTapes (Move Lmove;; Write (inl START)) [|Fin0|]) true | _ => Return Nop default (* invalid input *) end).
Definition Skip_cons_Rel : pRel (sigList sigX)^+ unit 1 := Mk_R_p ( ignoreParam ( fun tin tout => forall ls rs (x : X) (l : list X), tin = midtape (inl START :: ls) (inr sigList_cons) (map inr (Encode_map _ _ x) ++ map inr (Encode_map _ _ l) ++ inl STOP :: rs) -> match l with | nil => tout = midtape (rev (map inr (Encode_map _ _ x)) ++ inr sigList_cons :: inl START :: ls) (inr sigList_nil) (inl STOP :: rs) | x'::l' => tout = midtape (rev (map inr (Encode_map _ _ x)) ++ inr sigList_cons :: inl START :: ls) (inr sigList_cons) (map inr (Encode_map _ _ x') ++ map inr (Encode_map _ _ l') ++ inl STOP :: rs) end)).
Definition M1_Rel : pRel (sigList sigX)^+ unit 2 := ignoreParam ( fun tin tout => forall ls rs (x : X) (l : list X) (s1 : nat), tin[@Fin0] = midtape (inl START :: ls) (inr sigList_cons) (map inr (Encode_map _ _ x) ++ map inr (Encode_map _ _ l) ++ inl STOP :: rs) -> isVoid_size tin[@Fin1] s1 -> tout[@Fin0] = tin[@Fin0] /\ tout[@Fin1] ≃(; s1 - (S (size x))) x).
Definition CaseList_size0 {sigX X : Type} {cX : codable sigX X} (x : X) (s0 : nat) := S (s0 + size x).
Definition CaseList_size1 {sigX X : Type} {cX : codable sigX X} (x : X) (s1 : nat) := s1 - (S (size x)).
Definition CaseList_Rel : pRel (sigList sigX)^+ bool 2 := fun tin '(yout, tout) => forall (l : list X) (s0 s1 : nat), tin[@Fin0] ≃(;s0) l -> isVoid_size tin[@Fin1] s1 -> match yout, l with | false, nil => tout[@Fin0] ≃(;s0) @nil X /\ isVoid_size tout[@Fin1] s1 | true, x :: l' => tout[@Fin0] ≃(; CaseList_size0 x s0) l' /\ tout[@Fin1] ≃(; CaseList_size1 x s1) x | _, _ => False end.
Definition CaseList_steps_cons {sigX X : Type} {cX : codable sigX X} (x : X) := 42 + 16 *size x.
Definition CaseList_steps_nil := 5.
Definition CaseList_steps {sigX X : Type} {cX : codable sigX X} (l:list X) := match l with | nil => CaseList_steps_nil | x::l' => CaseList_steps_cons x end.
Definition IsNil : pTM (sigList sigX)^+ bool 1 := Move Rmove;; Switch ReadChar (fun s => match s with | Some (inr sigList_nil) => Return (Move Lmove) true | _ => Return (Move Lmove) false end).
Definition IsNil_Rel : pRel (sigList sigX)^+ bool 1 := Mk_R_p ( fun tin '(yout, tout) => forall (xs : list X) (s : nat), tin ≃(;s) xs -> match yout, xs with | true, nil => tout ≃(;s) xs | false, _ :: _ => tout ≃(;s) xs | _, _ => False end).
Definition IsNil_steps := 5.
Definition Constr_nil : pTM (sigList sigX)^+ unit 1 := WriteValue (@nil X).
Goal Constr_nil = WriteMove (inl STOP) Lmove;; WriteMove (inr sigList_nil) Lmove;; Write (inl START).
Proof.
reflexivity.
Definition Constr_nil_Rel : pRel (sigList sigX)^+ unit 1 := Mk_R_p (ignoreParam (fun tin tout => forall (s : nat), isVoid_size tin s -> tout ≃(; pred s) @nil X)).
Definition Constr_nil_steps := 5.
Definition Constr_cons : pTM (sigList sigX)^+ unit 2 := LiftTapes (MoveRight _;; Move Lmove) [|Fin1|];; LiftTapes (CopySymbols_L stop) [|Fin1;Fin0|];; LiftTapes (WriteMove (inr sigList_cons) Lmove;; Write (inl START)) [|Fin0|].
Definition Constr_cons_size {sigX X : Type} {cX : codable sigX X} (y : X) (s0 : nat) := s0 - size y - 1.
Definition Constr_cons_Rel : pRel (sigList sigX)^+ unit 2 := ignoreParam ( fun tin tout => forall (l:list X) (y:X) (s0 s1 : nat), tin[@Fin0] ≃(;s0) l -> tin[@Fin1] ≃(;s1) y -> tout[@Fin0] ≃(;Constr_cons_size y s0) y :: l /\ tout[@Fin1] ≃(;s1) y ).
Definition Constr_cons_steps {sigX X : Type} {cX : codable sigX X} (x : X) := 23 + 12 * size x.
End CaseList.
Arguments CaseList : simpl never.
Arguments IsNil : simpl never.
Arguments Constr_nil _ {_ _}: simpl never.
Arguments Constr_cons : simpl never.
Arguments CaseList_size0 {sigX X cX} : simpl never.
Arguments CaseList_size1 {sigX X cX} : simpl never.
Arguments Constr_cons_size {sigX X cX} : simpl never.
Arguments CaseList_steps_cons {sigX X cX} : simpl never.
Arguments CaseList_steps {sigX X cX} : simpl never.
Arguments Constr_cons_steps {sigX X cX} : simpl never.
Arguments CaseList_steps_nil : simpl never.
Ltac smpl_TM_CaseList := once lazymatch goal with | [ |- CaseList _ ⊨ _ ] => apply CaseList_Realise | [ |- projT1 (CaseList _) ↓ _ ] => apply CaseList_Terminates | [ |- IsNil _ ⊨ _ ] => eapply RealiseIn_Realise; apply IsNil_Sem | [ |- IsNil _ ⊨c(_) _ ] => apply IsNil_Sem | [ |- projT1 (IsNil _ ) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply IsNil_Sem | [ |- Constr_nil _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_nil_Sem | [ |- Constr_nil _ ⊨c(_) _ ] => apply Constr_nil_Sem | [ |- projT1 (Constr_nil _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_nil_Sem | [ |- Constr_cons _ ⊨ _ ] => apply Constr_cons_Realise | [ |- projT1 (Constr_cons _) ↓ _ ] => apply Constr_cons_Terminates end.
Smpl Add smpl_TM_CaseList : TM_Correct.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister HoareTactics.
Section CaseList.
Variable (X : Type) (sigX : finType) (codX : codable sigX X).
Definition Constr_cons_sizefun (x : X) : Vector.t (nat->nat) 2 := [|Constr_cons_size x; id|].
Definition CaseList_size (xs : list X) : Vector.t (nat->nat) 2 := match xs with | nil => [|id;id|] | x :: xs => [|CaseList_size0 x; CaseList_size1 x|] end.
End CaseList.
Ltac hstep_List := match goal with | [ |- TripleT ?P ?k (Constr_cons _) ?Q ] => eapply Constr_cons_SpecT_size | [ |- TripleT ?P ?k (Constr_nil _) ?Q ] => eapply Constr_nil_SpecT_size | [ |- TripleT ?P ?k (CaseList _) ?Q ] => eapply CaseList_SpecT_size end.
Smpl Add hstep_List : hstep_Spec.

Lemma CaseList_Realise : CaseList ⊨ CaseList_Rel.
Proof.
eapply Realise_monotone.
{
unfold CaseList.
TM_Correct.
eapply M1_Realise.
eapply Skip_cons_Realise.
}
{
intros tin (yout, tout) H.
intros l s0 s1 HEncL HRight.
unfold CaseList_size0, CaseList_size1 in *.
destruct HEncL as (ls&HEncL&Hs0).
pose proof HRight as (ls'&rs'&HRight'&Hs1).
TMSimp; clear_trivial_eqs.
destruct l as [ | x l'] in *; cbn in *; TMSimp; clear_trivial_eqs.
{
split; auto.
-
repeat econstructor; cbn; simpl_tape.
auto.
}
{
rewrite !map_map, map_app, <- app_assoc in *.
setoid_rewrite map_map in H.
setoid_rewrite map_map in H0.
specialize H with (1 := eq_refl) (2 := HRight).
TMSimp.
specialize H0 with (1 := eq_refl).
destruct l' as [ | x' l'']; TMSimp.
-
repeat split; auto.
hnf.
eexists.
split.
simpl_tape.
f_equal.
+
rewrite tl_length.
simpl_list.
cbn.
unfold size.
lia.
-
repeat split; auto.
hnf.
eexists.
simpl_tape.
rewrite List.map_map.
cbn.
simpl_list.
split.
+
f_equal.
f_equal.
now rewrite !map_map.
+
rewrite tl_length.
simpl_list.
cbn.
unfold size.
lia.
}
}

Require Import Undecidability.Shared.Libs.PSL.Bijection.
From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import TM.Code.CompareValue.
From Undecidability Require Import TM.Code.CasePair TM.Code.CaseList.
From Undecidability.TM.Hoare Require Import Hoare HoareLegacy.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Set Default Proof Using "Type".
Section LookupAssociativeList.
Variable (sigX sigY : finType).
Variable (X : eqType) (Y : Type) (cX : codable sigX X) (cY : codable sigY Y).
Notation sig := (sigList (sigPair sigX sigY)).
Hypothesis (cX_injective : injective cX).
Fixpoint lookup (x : X) (xs : list (X * Y)) {struct xs} : option Y := match xs with | nil => None | (x', y) :: xs' => if Dec (x = x') then Some y else lookup x xs' end.
Local Definition retr_sig_sigX : Retract sigX sig := _.
Local Definition retr_sig_sigY : Retract sigY sig := _.
Definition Lookup_Step : pTM sig^+ (option bool) 4 := If (CaseList (FinType(EqType(sigPair sigX sigY))) @ [|Fin0; Fin2|] ) (CasePair _ _ ⇑ _ @ [|Fin2; Fin3|];; If (CompareValues _ ⇑ retr_sig_sigX @ [|Fin1; Fin3|]) (Return (MoveValue _ @ [|Fin2; Fin1|];; Reset _ @ [|Fin3|];; Reset _ @ [|Fin0|]) (Some true)) (Return (Reset _ @ [|Fin3|];; Reset _ @ [|Fin2|]) None)) (Return (ResetEmpty1 _ @ [|Fin0|]) (Some false)).
Definition Lookup_Step_size {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x:X) : Vector.t (nat->nat) 4 := match xs with | (x', y) :: xs' => if Dec (x=x') then [| (*0*) CaseList_size0 (x', y) >> Reset_size xs'; (*1*) MoveValue_size_y y x; (* [CompareValue] doesn't use space *) (*2*) CaseList_size1 (x', y) >> CasePair_size0 x' >> MoveValue_size_x y; (*3*) CasePair_size1 x' >> Reset_size x' |] else [| (*0*) CaseList_size0 (x',y); (*1*) id; (* [CompareValue] doesn't use space *) (*2*) CaseList_size1 (x',y) >> CasePair_size0 x' >> Reset_size y; (*3*) CasePair_size1 x' >> Reset_size x' |] | nil => [| ResetEmpty1_size; id; id; id|] end.
Definition Lookup_Step_steps_Compare {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (x x' : X) (y : Y) (xs : list (X*Y)) := if Dec (x=x') then 2 + MoveValue_steps y x + Reset_steps x' + Reset_steps xs else 1 + Reset_steps x' + Reset_steps y.
Definition Lookup_Step_steps_CaseList {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) := match xs with | nil => ResetEmpty1_steps | (x',y) :: xs' => 2 + CompareValues_steps x x' + CasePair_steps x' + Lookup_Step_steps_Compare x x' y xs' end.
Definition Lookup_Step_steps {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) := 1 + CaseList_steps xs + Lookup_Step_steps_CaseList xs x.
Definition Lookup_Loop := While Lookup_Step.
Fixpoint Lookup_Loop_size {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) : Vector.t (nat->nat) 4 := match xs with | nil => Lookup_Step_size xs x | (x',y) :: xs' => if Dec(x=x') then Lookup_Step_size xs x else Lookup_Step_size xs x >>> Lookup_Loop_size xs' x end.
Fixpoint Lookup_Loop_steps {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (xs : list (X*Y)) { struct xs } := match xs with | nil => Lookup_Step_steps xs x | (x',y) :: xs' => if Dec(x=x') then Lookup_Step_steps xs x else 1 + Lookup_Step_steps xs x + Lookup_Loop_steps x xs' end.
Definition Lookup : pTM sig^+ bool 5 := CopyValue _ @ [|Fin0; Fin4|];; Lookup_Loop @ [|Fin4; Fin1; Fin2; Fin3|].
Definition Lookup_size {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) : Vector.t (nat->nat) 5 := ([|CopyValue_size xs|] @>> [|Fin4|]) >>> (Lookup_Loop_size xs x @>>[|Fin4; Fin1; Fin2; Fin3|]).
Definition Lookup_Rel : pRel sig^+ bool 5 := fun tin '(yout, tout) => forall (xs : list (X*Y)) (x : X) (s0 s1 s2 s3 s4 : nat), let size := Lookup_size xs x in tin[@Fin0] ≃(;s0) xs -> tin[@Fin1] ≃(;s1) x -> isVoid_size tin[@Fin2] s2 -> isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 -> match yout, lookup x xs with | true, Some y => tout[@Fin0] ≃(;size@>Fin0 s0) xs /\ tout[@Fin1] ≃(;size@>Fin1 s1) y /\ isVoid_size tout[@Fin2] (size@>Fin2 s2) /\ isVoid_size tout[@Fin3] (size@>Fin3 s3) /\ isVoid_size tout[@Fin4] (size@>Fin4 s4) | false, None => tout[@Fin0] ≃(;size@>Fin0 s0) xs /\ tout[@Fin1] ≃(;size@>Fin1 s1) x /\ isVoid_size tout[@Fin2] (size@>Fin2 s2) /\ isVoid_size tout[@Fin3] (size@>Fin3 s3) /\ isVoid_size tout[@Fin4] (size@>Fin4 s4) | _, _ => False end.
Definition Lookup_steps {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (xs : list (X*Y)) := 1 + CopyValue_steps xs + Lookup_Loop_steps x xs.
Definition Lookup_T : tRel sig^+ 5 := fun tin k => exists (xs : list (X*Y)) (x : X), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ x /\ isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\ isVoid tin[@Fin4] /\ Lookup_steps x xs <= k.
End LookupAssociativeList.
Arguments Lookup_steps {sigX sigY X Y cX cY} : simpl never.
Arguments Lookup_size {sigX sigY X Y cX cY} : simpl never.
Ltac hstep_LookupAssociativeList := match goal with | [ |- TripleT ?P ?k (Lookup _ _) ?Q ] => eapply Lookup_SpecT_space end.

Lemma Lookup_SpecT_space (xs : list (X*Y)) (x : X) (ss : Vector.t nat 5) : TripleT (≃≃([],withSpace ([|Contains _ xs; Contains _ x; Void; Void; Void|]) ss)) (Lookup_steps x xs) Lookup (fun yout => tspec ([yout = match lookup x xs with Some y => true | _ => false end], withSpace [|Contains _ xs; (match lookup x xs with Some y => Contains _ y | _ => Contains _ x end); Void; Void; Void|] (appSize (Lookup_size xs x) ss))).
Proof using cX_injective.
start_TM.
unfold Lookup.
hsteps_cbn; cbn.
apply Lookup_Loop_SpecT_space.
intros yout;cbn.
hintros ->.
destruct (lookup x xs); cbn.
1-2:now tspec_ext.
reflexivity.

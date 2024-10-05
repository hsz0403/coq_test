From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import ArithPrelim.
From Undecidability Require Import TM.Compound.Shift.
From Undecidability Require Import TM.Util.VectorPrelim.
From Undecidability Require Import EncodeTapes TM.Util.VectorPrelim.
Require Import FunInd.
Local Set Printing Coercions.
Local Arguments Vector.to_list {A n} (!v).
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Section Fin.
Global Coercion fin_to_nat (n : nat) (i : Fin.t n) : nat := proj1_sig (Fin.to_nat i).
Global Set Printing Coercions.
Fixpoint finMax (n : nat) {struct n} : n <> 0 -> Fin.t n.
Proof.
destruct n as [ | n'].
-
abstract congruence.
-
decide (n' = 0) as [ H | H].
+
intros _.
apply Fin.F1.
+
intros _.
apply Fin.FS.
apply (finMax n').
auto.
Defined.
Definition finMax' (n : nat) : Fin.t (S n).
Proof.
apply finMax.
apply Nat.neq_succ_0.
Defined.
Definition finMin (n : nat) : n <> 0 -> Fin.t n.
Proof.
refine (match n as n' return n' <> 0 -> Fin.t n' with | 0 => fun H => False_rec _ _ | S n' => fun _ => Fin.F1 end); auto.
Defined.
Fixpoint finSucc (n : nat) (i : Fin.t n) {struct n} : forall (H : n <> 0), i <> finMax H -> Fin.t n.
Proof.
destruct n as [ | n'].
-
intros.
abstract congruence.
-
cbn.
decide (n' = 0) as [ HDec | HDec]; cbn.
+
intros _ Hi.
exfalso.
apply Hi.
subst.
apply finSucc_help.
+
intros _.
revert n' i HDec.
refine (@Fin.caseS (fun n' i => forall (HDec : n' <> 0), i <> Fin.FS (finMax HDec) -> Fin.t (S n')) _ _).
*
intros.
apply Fin.FS.
apply finMin.
apply HDec.
*
intros.
apply Fin.FS.
eapply finSucc.
eapply finSucc_help'.
apply H.
Defined.
Definition finSucc' (n : nat) (i : Fin.t (S n)) (H : i <> finMax' n) : Fin.t (S n).
Proof.
unshelve eapply finSucc with (i := i).
apply Nat.neq_succ_0.
apply H.
Defined.
Fixpoint finSucc_opt (n : nat) (i : Fin.t n) {struct i} : option (Fin.t n).
Proof.
destruct i.
-
destruct n.
+
apply None.
+
apply Some.
apply Fin.FS.
apply Fin.F1.
-
destruct n.
+
destruct_fin i.
+
destruct (finSucc_opt _ i) as [ rec | ].
*
apply Some.
apply Fin.FS.
apply rec.
*
apply None.
Defined.
Definition finMin_opt (n : nat) : option (Fin.t n).
Proof.
destruct n.
-
apply None.
-
apply Some.
apply Fin.F1.
Defined.
End Fin.
Fixpoint map_vect_list (X Y : Type) (f : X -> Y -> X) (n : nat) (vs : Vector.t Y n) (ls : list X) {struct ls} : list X := match ls with | nil => nil | x :: ls' => match vs with | [| |] => ls | y ::: vs' => f x y :: map_vect_list f vs' ls' end end.
Section BookKeepingForRead.
Variable sig : Type.
Set Default Proof Using "Type".
Fixpoint knowsFirstSymbols {n' : nat} (readSymbols : Vector.t (option sig) n') (tps : list (tape sig)) {struct readSymbols} : Prop := match readSymbols, tps with | Vector.nil _, nil => True /\ True /\ True | Vector.nil _, _::_ => True /\ True (* to much tapes *) | x ::: readSymbols, nil => True (* list of tapes is too big, must not happen *) | x ::: readSymbols', tp :: tps' => current tp = x /\ knowsFirstSymbols readSymbols' tps' end.
Definition insertKnownSymbol {n : nat} (readSymbols : Vector.t (option sig) n) (i : Fin.t n) (s : option sig) : Vector.t (option sig) n := Vector.replace readSymbols i s.
Fixpoint insertKnownSymbols {n : nat} (readSymbols : Vector.t (option sig) n) (i : Fin.t n) (newSymbols : list (option sig)) : Vector.t (option sig) n := match newSymbols with | nil => readSymbols | s :: newSymbols' => match finSucc_opt i with | Some i' => insertKnownSymbols (insertKnownSymbol readSymbols i s) i' newSymbols' | None => insertKnownSymbol readSymbols i s end end.
End BookKeepingForRead.
Section ToSingleTape.
Variable (sig F : finType).
Variable n : nat.
Notation nMax := (finMax' n).
Local Arguments finMax' : simpl never.
Notation sigSim := (FinType(EqType(boundary + sigList (sigTape sig)))).
Implicit Types (T : tapes sig n).
Definition contains_tapes (t : tape sigSim) T := t = midtape nil (inl START) (map inr (encode_tapes T) ++ [inl STOP]).
Notation "t ≃ T" := (contains_tapes t T) (at level 70, no associativity).
Hypothesis pM : pTM sig F n.
Section GoToCurrent.
Definition atStart (t : tape sigSim) (tps : list (tape sig)) : Prop := t = midtape nil (inl START) (map inr (encode_list _ tps) ++ [inl STOP]).
Definition atCons (t : tape sigSim) (tps1 tps2 : list (tape sig)) (tp : tape sig) : Prop := t = midtape (map inr (rev (removelast (encode_list _ tps1))) ++ [inl START]) (inr (sigList_cons)) (map inr (map sigList_X (encode_tape tp)) ++ map inr (encode_list _ tps2) ++ [inl STOP]).
Definition atNil (t : tape sigSim) (tps : list (tape sig)) : Prop := t = midtape (map inr (rev (removelast (encode_list _ tps))) ++ [inl START]) (inr (sigList_nil)) [inl STOP].
Definition atCons_current_niltape (t : tape sigSim) (tps1 tps2 : list (tape sig)) : Prop := t = midtape (inr (sigList_cons) :: map inr (rev (removelast (encode_list _ tps1))) ++ [inl START]) (inr (sigList_X NilBlank)) (map inr (encode_list _ tps2) ++ [inl STOP]).
Definition atCons_current_leftof (t : tape sigSim) (tps1 tps2 : list (tape sig)) (r : sig) (rs : list sig) := t = midtape (inr (sigList_cons) :: map inr (rev (removelast (encode_list _ tps1))) ++ [inl START]) (inr (sigList_X (LeftBlank true))) (inr (sigList_X (UnmarkedSymbol r)) :: map (fun s => inr (sigList_X (UnmarkedSymbol s))) rs ++ inr (sigList_X (RightBlank false)) :: map inr (encode_list _ tps2) ++ [inl STOP]).
Definition atCons_current_midtape (t : tape sigSim) (tps1 tps2 : list (tape sig)) (ls : list sig) (m : sig) (rs : list sig) := t = midtape (map (fun s => inr (sigList_X (UnmarkedSymbol s))) ls ++ (* [ls] is reversed twice *) inr (sigList_X (LeftBlank false)) :: inr (sigList_cons) :: map inr (rev (removelast (encode_list _ tps1))) ++ [inl START]) (inr (sigList_X (MarkedSymbol m))) (map (fun s => inr (sigList_X (UnmarkedSymbol s))) rs ++ inr (sigList_X (RightBlank false)) :: map inr (encode_list _ tps2) ++ [inl STOP]).
Definition atCons_current_rightof (t : tape sigSim) (tps1 tps2 : list (tape sig)) (l :sig) (ls : list sig) := t = midtape (inr (sigList_X (UnmarkedSymbol l)) :: map (fun s => inr (sigList_X (UnmarkedSymbol s))) ls ++ (* [ls] is reversed twice *) inr (sigList_X (LeftBlank false)) :: inr (sigList_cons) :: map inr (rev (removelast (encode_list _ tps1))) ++ [inl START]) (inr (sigList_X (RightBlank true))) (map inr (encode_list _ tps2) ++ [inl STOP]).
Definition atCons_current (t : tape sigSim) (tps1 tps2 : list (tape sig)) (tp : tape sig) := match tp with | niltape _ => atCons_current_niltape t tps1 tps2 | leftof r rs => atCons_current_leftof t tps1 tps2 r rs | midtape ls m rs => atCons_current_midtape t tps1 tps2 ls m rs | rightof l ls => atCons_current_rightof t tps1 tps2 l ls end.
Definition tape_dir (t : tape sig) : option move := match t with | niltape _ => None | leftof _ _ => Some Lmove | midtape _ _ _ => Some Nmove | rightof _ _ => Some Rmove end.
Definition isMarked' (s : sigSim) : bool := match s with | inr (sigList_X s) => isMarked s | _ => false end.
Definition IsCons_Rel : pRel sigSim bool 1 := fun tin '(yout, tout) => (forall tps1 tps2 tp, atCons tin[@Fin0] tps1 tps2 tp -> atCons tout[@Fin0] tps1 tps2 tp /\ yout = true) /\ (forall tps, atNil tin[@Fin0] tps -> atNil tout[@Fin0] tps /\ yout = false).
Definition IsCons : pTM sigSim bool 1 := Switch ReadChar (fun (s : option sigSim) => match s with | Some (inr (sigList_cons)) => Return Nop true | Some (inr (sigList_nil)) => Return Nop false | _ => Return Nop default end).
Definition IsCons_steps := 2.
Definition GoToCurrent_Rel : pRel sigSim (option move) 1 := fun tin '(yout, tout) => forall (tps1 tps2 : list (tape sig)) (tp : tape sig), atCons tin[@Fin0] tps1 tps2 tp -> atCons_current tout[@Fin0] tps1 tps2 tp /\ yout = tape_dir tp.
Definition GoToCurrent : pTM sigSim (option move) 1 := MoveToSymbol isMarked' id;; Switch ReadChar (fun (c : option sigSim) => match c with | Some (inr (sigList_X (RightBlank true))) => Return Nop (Some Rmove) | Some (inr (sigList_X (LeftBlank true))) => Return Nop (Some Lmove) | Some (inr (sigList_X (MarkedSymbol _))) => Return Nop (Some Nmove) | Some (inr (sigList_X NilBlank)) => Return Nop (None) | _ => Return Nop None end).
Definition GoToCurrent_steps' (tp : tape sig) := match tp with | niltape _ => 8 | leftof r rs => 8 | rightof l ls => 16 + 4 * length ls | midtape ls m rs => 16 + 4 * length ls end.
Definition GoToCurrent_steps (tp : tape sig) := GoToCurrent_steps' tp + 3.
Definition GoToCurrent_T : tRel sigSim 1 := fun tin k => exists tps1 tps2 tp, atCons tin[@Fin0] tps1 tps2 tp /\ GoToCurrent_steps tp <= k.
End GoToCurrent.
Section GoToNext.
Definition GoToNext_Rel : pRel sigSim bool 1 := fun tin '(yout, tout) => forall tps1 tps2 tp, atCons_current tin[@Fin0] tps1 tps2 tp -> match yout, tps2 with | true, tp' :: tps2' => atCons tout[@Fin0] (tps1 ++ [tp]) tps2' tp' | false, nil => atNil tout[@Fin0] (tps1 ++ [tp]) | _, _ => False end.
Definition isNilCons : sigSim -> bool := fun s => match s with | inr sigList_nil => true | inr sigList_cons => true | _ => false end.
Definition GoToNext : pTM sigSim bool 1 := MoveToSymbol isNilCons id;; IsCons.
Definition GoToNext_steps' (t : tape sig) := match t with | niltape _ => 8 | leftof r rs => 16 + 4 * length rs | rightof r rs => 8 | midtape ls m rs => 16 + 4 * length rs end.
Definition GoToNext_steps (tp : tape sig) := GoToNext_steps' tp + 3.
Definition GoToNext_T : tRel sigSim 1 := fun tin k => exists tps1 tps2 tp, atCons_current tin[@Fin0] tps1 tps2 tp /\ GoToNext_steps tp <= k.
End GoToNext.
Section ReadCurrentSymbols.
Local Arguments insertKnownSymbol : simpl never.
Definition ReadCurrent : pTM sigSim (option sig) 1 := Switch ReadChar (fun (s : option sigSim) => match s with | Some (inr (sigList_X (MarkedSymbol s))) => Return Nop (Some s) | _ => Return Nop None end).
Definition ReadCurrent_Rel : pRel sigSim (option sig) 1 := fun tin '(yout, tout) => forall tps1 tps2 tp, atCons_current tin[@Fin0] tps1 tps2 tp -> atCons_current tout[@Fin0] tps1 tps2 tp /\ yout = current tp.
Definition ReadCurrent_steps := 2.
Definition ReadCurrentSymbols_Step_Rel (st : Vector.t (option sig) n * Fin.t n) : pRel sigSim (Vector.t (option sig) n * Fin.t n + Vector.t (option sig) n) 1 := fun tin '(yout, tout) => (forall tps1 tps2 tp , (length tps1 =? fin_to_nat (snd st)) = true -> (length tps1 + (1 + length tps2) =? n) = true -> atCons tin[@Fin0] tps1 tps2 tp -> knowsFirstSymbols (fst st) tps1 -> match tps2 with | nil => atNil tout[@Fin0] (tps1 ++ [tp]) /\ yout = inr (insertKnownSymbol (fst st) (snd st) (current tp)) | tp' :: tps2' => atCons tout[@Fin0] (tps1 ++ [tp]) tps2' tp' /\ match finSucc_opt (snd st) with | Some i' => yout = inl (insertKnownSymbol (fst st) (snd st) (current tp), i') | None => False end end) /\ (forall tps, atNil tin[@Fin0] tps -> atNil tout[@Fin0] tps /\ yout = inr (fst st)).
Definition ReadCurrentSymbols_Step : forall (st : Vector.t (option sig) n * Fin.t n), pTM sigSim (Vector.t (option sig) n * Fin.t n + Vector.t (option sig) n) 1 := fun '(readSymbols, i) => If IsCons (GoToCurrent;; Switch (ReadCurrent) (fun (c : option sig) => Return (GoToNext) (match finSucc_opt i with | None => inr (insertKnownSymbol readSymbols i c) | Some i' => inl (insertKnownSymbol readSymbols i c, i') end))) (Return Nop (inr readSymbols)).
Definition ReadCurrentSymbols_Step_steps_cons tp := 3 + IsCons_steps + GoToCurrent_steps tp + ReadCurrent_steps + GoToNext_steps tp.
Definition ReadCurrentSymbols_Step_steps_nil := 1 + IsCons_steps.
Definition ReadCurrentSymbols_Step_T : tRel sigSim 1 := fun tin k => (exists tps1 tps2 tp, atCons tin[@Fin0] tps1 tps2 tp /\ ReadCurrentSymbols_Step_steps_cons tp <= k) \/ (exists tps, atNil tin[@Fin0] tps /\ ReadCurrentSymbols_Step_steps_nil <= k).
Definition ReadCurrentSymbols_Loop := StateWhile ReadCurrentSymbols_Step.
Definition ReadCurrentSymbols_Loop_Rel (st : Vector.t (option sig) n * Fin.t n) : pRel sigSim (Vector.t (option sig) n) 1 := fun tin '(yout, tout) => (forall tps1 tp tps2, (length tps1 =? fin_to_nat (snd st)) = true -> (length tps1 + (1 + length tps2) =? n) = true -> atCons tin[@Fin0] tps1 tps2 tp -> knowsFirstSymbols (fst st) tps1 -> atNil tout[@Fin0] (tps1 ++ tp :: tps2) /\ yout = insertKnownSymbols (fst st) (snd st) (current tp :: map (@current _) tps2)) /\ (forall tps, (length tps =? n) = true -> atNil tin[@Fin0] tps -> knowsFirstSymbols (fst st) tps -> atNil tout[@Fin0] tps /\ yout = (fst st)).
Definition ReadCurrentSymbols_Loop_steps_nil := ReadCurrentSymbols_Step_steps_nil.
Fixpoint ReadCurrentSymbols_Loop_steps_cons tps2 tp := match tps2 with | nil => ReadCurrentSymbols_Step_steps_cons tp | tp' :: tps2' => 1 + ReadCurrentSymbols_Step_steps_cons tp + ReadCurrentSymbols_Loop_steps_cons tps2' tp' end.
Definition ReadCurrentSymbols_Loop_T (st : Vector.t (option sig) n * Fin.t n) : tRel sigSim 1 := fun tin k => (exists tps1 tps2 tp, (length tps1 =? fin_to_nat (snd st)) = true /\ (length tps1 + (1 + length tps2) =? n) = true /\ knowsFirstSymbols (fst st) tps1 /\ atCons tin[@Fin0] tps1 tps2 tp /\ ReadCurrentSymbols_Loop_steps_cons tps2 tp <= k) \/ (exists tps, atNil tin[@Fin0] tps /\ ReadCurrentSymbols_Loop_steps_nil <= k).
Definition ReadCurrentSymbols := match (finMin_opt n) with | None => Return (Move Rmove) (Vector.const None n) (* Nothing to do, just move from the start to the nil symbol *) | Some min => Move Rmove;; ReadCurrentSymbols_Loop (Vector.const None n, min) end.
Definition ReadCurrentSymbols_Rel : pRel sigSim (Vector.t (option sig) n) 1 := fun tin '(yout, tout) => forall T, tin[@Fin0] ≃ T -> atNil tout[@Fin0] (vector_to_list T) /\ yout = current_chars T.
Definition ReadCurrentSymbols_steps (n : nat) (T : tapes sig n) := match T with | [| |] => ReadCurrentSymbols_Loop_steps_nil | tp ::: T' => 2 + ReadCurrentSymbols_Loop_steps_cons (vector_to_list T') tp end.
Definition ReadCurrentSymbols_T : tRel sigSim 1 := fun tin k => exists T, tin[@Fin0] ≃ T /\ ReadCurrentSymbols_steps T <= k.
End ReadCurrentSymbols.
Section MoveToStart.
Definition MoveToStart_Rel : pRel sigSim unit 1 := ignoreParam (fun tin tout => forall tps, atNil tin[@Fin0] tps -> atStart tout[@Fin0] tps).
Definition isStart : sigSim -> bool := fun s => match s with | inl START => true | _ => false end.
Definition MoveToStart : pTM sigSim unit 1 := MoveToSymbol_L isStart id.
Definition MoveToStart_steps (tps : list (tape sig)) := 8 + 4 * length (encode_list _ tps).
Definition MoveToStart_T : tRel sigSim 1 := fun tin k => exists tps, atNil tin[@Fin0] tps /\ MoveToStart_steps tps <= k.
End MoveToStart.
Section DoActions.
Variable (acts : Vector.t (option sig * move) n).
Definition isReturnMarker (s : sigSim) : bool := match s with | inl UNKNOWN => true | _ => false end.
Definition DoWrite_Rel (d : option move) (s : sig) : pRel sigSim unit 1 := ignoreParam (fun tin tout => forall tps1 tps2 tp, tape_dir tp = d -> atCons_current tin[@Fin0] tps1 tps2 tp -> atCons_current tout[@Fin0] tps1 tps2 (tape_write tp (Some s))).
Definition DoWrite (d : option move) (s : sig) : pTM sigSim unit 1 := match d with | Some Lmove => (* [leftof] ~> shift left and change boundary symbol to [LeftBlank false] *) Shift_L (fun _ => false) (inl UNKNOWN);; MoveToSymbol isReturnMarker id;; WriteMove (inr (sigList_X (MarkedSymbol s))) Lmove;; WriteMove (inr (sigList_X (LeftBlank false))) Rmove | Some Rmove => (* [rightof] ~> shift right and change boundary symbol to [RightBlank false] *) Shift (fun _ => false) (inl UNKNOWN);; MoveToSymbol_L isReturnMarker id;; WriteMove (inr (sigList_X (MarkedSymbol s))) Rmove;; WriteMove (inr (sigList_X (RightBlank false))) Lmove | Some Nmove => (* [midtape] ~> just write the symbol *) Write (inr (sigList_X (MarkedSymbol s))) | None => (* [midtape] ~> we need to shift left and right and insert [RightBlank false] and [LeftBlank false] *) Shift (fun _ => false) (inl UNKNOWN);; MoveToSymbol_L isReturnMarker id;; Shift_L (fun _ => false) (inr (sigList_X (MarkedSymbol s)));; MoveToSymbol isReturnMarker id;; WriteMove (inr (sigList_X (LeftBlank false))) Rmove;; Move Rmove;; WriteMove (inr (sigList_X (RightBlank false))) Lmove end.
Definition DoWrite_steps (d : option move) (tps1 tps2 : list (tape sig)) := match d with | Some Lmove => 37 + 8 * length (encode_list _ tps1) | Some Rmove => 37 + 8 * length (encode_list _ tps2) | Some Nmove => 1 | None => 73 + 8 * length (encode_list _ tps1) + 8 * length (encode_list _ tps2) end.
Definition DoWrite_T (d : option move) : tRel sigSim 1 := fun tin k => exists tps1 tps2 tp, tape_dir tp = d /\ atCons_current tin[@Fin0] tps1 tps2 tp /\ DoWrite_steps d tps1 tps2 <= k.
Definition DoMove_Rel (d : option move) (m : move) : pRel sigSim unit 1 := ignoreParam (fun tin tout => forall tps1 tps2 tp, tape_dir tp = d -> atCons_current tin[@Fin0] tps1 tps2 tp -> atCons_current tout[@Fin0] tps1 tps2 (tape_move tp m)).
Definition toggle_marked (s : sigTape sig) : sigTape sig := match s with | UnmarkedSymbol s => MarkedSymbol s | MarkedSymbol s => UnmarkedSymbol s | LeftBlank b => LeftBlank (negb b) | RightBlank b => RightBlank (negb b) | NilBlank => NilBlank end.
Definition ToggleMarked_Rel : pRel sigSim unit 1 := ignoreParam (fun tin tout => forall ls m rs, tin[@Fin0] = midtape ls (inr (sigList_X m)) rs -> tout[@Fin0] = midtape ls (inr (sigList_X (toggle_marked m))) rs).
Definition ToggleMarked : pTM sigSim unit 1 := Switch ReadChar (fun (s : option sigSim) => match s with | Some (inr (sigList_X m)) => Write (inr (sigList_X (toggle_marked m))) | _ => Nop end).
Definition DoMove (d : option move) (m : move) : pTM sigSim unit 1 := match d with | Some Lmove => match m with | Nmove => Nop | Lmove => Nop | Rmove => ToggleMarked;; Move Rmove;; ToggleMarked end | Some Rmove => match m with | Nmove => Nop | Rmove => Nop | Lmove => ToggleMarked;; Move Lmove;; ToggleMarked end | Some Nmove => match m with | Nmove => Nop | Rmove => ToggleMarked;; Move Rmove;; ToggleMarked | Lmove => ToggleMarked;; Move Lmove;; ToggleMarked end | None => Nop end.
Definition DoMove_steps := 9.
Arguments DoMove : simpl never.
Definition DoAction_Rel (d : option move) (a : option sig * move) : pRel sigSim unit 1 := ignoreParam (fun tin tout => forall (tps1 tps2 : list (tape sig)) (tp : tape sig), tape_dir tp = d -> atCons_current tin[@Fin0] tps1 tps2 tp -> atCons_current tout[@Fin0] tps1 tps2 (doAct tp a)).
Definition DoAction (d : option move) (a : option sig * move) : pTM sigSim unit 1 := match (fst a) with | Some s => DoWrite d s;; DoMove (Some Nmove) (snd a) (* after wrting, we have a [midtape] *) | None => DoMove d (snd a) end.
Definition DoAction_steps (d : option move) (a : option sig * move) (tps1 tps2 : list (tape sig)) := match (fst a) with | Some s => 1 + DoWrite_steps d tps1 tps2 + DoMove_steps | None => DoMove_steps end.
Definition DoAction_T (d : option move) (a : option sig * move) : tRel sigSim 1 := fun tin k => exists tps1 tps2 tp, tape_dir tp = d /\ atCons_current tin[@Fin0] tps1 tps2 tp /\ DoAction_steps d a tps1 tps2 <= k.
Definition DoActions_Step_Rel (i : Fin.t n) : pRel sigSim (Fin.t n + unit) 1 := fun tin '(yout, tout) => (forall tps1 tps2 tp, (length tps1 =? fin_to_nat i) = true -> (length tps1 + (1 + length tps2) =? n) = true -> atCons tin[@Fin0] tps1 tps2 tp -> match tps2 with | tp' :: tps2' => atCons tout[@Fin0] (tps1 ++ [doAct tp acts[@i]]) tps2' tp' /\ match finSucc_opt i with | Some i' => yout = inl i' | None => False end | nil => atNil tout[@Fin0] (tps1 ++ [doAct tp acts[@i]]) /\ yout = inr tt end) /\ (forall tps, atNil tin[@Fin0] tps -> atNil tout[@Fin0] tps /\ yout = inr tt).
Definition opt_to_sum_unit (X : Type) (x : option X) : X + unit := match x with | Some x => inl x | None => inr tt end.
Definition DoActions_Step (i : Fin.t n) : pTM sigSim (Fin.t n + unit) 1 := If IsCons (Switch GoToCurrent (fun (d : option move) => Return (DoAction d (acts[@i]);; GoToNext) (opt_to_sum_unit (finSucc_opt i)))) (Return Nop (inr tt)).
Definition DoActions_Step_steps_cons i tps1 tps2 tp := 3 + IsCons_steps + GoToCurrent_steps tp + DoAction_steps (tape_dir tp) (acts[@i]) tps1 tps2 + GoToNext_steps (doAct tp acts[@i]).
Definition DoActions_Step_steps_nil := 1 + IsCons_steps.
Definition DoActions_Step_T (i : Fin.t n) : tRel sigSim 1 := fun tin k => (exists tps1 tps2 tp, (length tps1 =? fin_to_nat i) = true /\ (length tps1 + (1 + length tps2) =? n) = true /\ atCons tin[@Fin0] tps1 tps2 tp /\ DoActions_Step_steps_cons i tps1 tps2 tp <= k) \/ (exists tps, atNil tin[@Fin0] tps /\ DoActions_Step_steps_nil <= k).
Definition DoActions_Loop : Fin.t n -> pTM sigSim unit 1 := StateWhile DoActions_Step.
Definition DoActions_Loop_Rel (i : Fin.t n) : pRel sigSim unit 1 := fun tin '(yout, tout) => (forall tps1 tps2 tp, (length tps1 =? fin_to_nat i) = true -> (length tps1 + (1 + length tps2) =? n) = true -> atCons tin[@Fin0] (map_vect_list (@doAct sig) acts tps1) tps2 tp -> atNil tout[@Fin0] (map_vect_list (@doAct sig) acts (tps1 ++ tp :: tps2)) ) /\ (forall tps, atNil tin[@Fin0] tps -> atNil tout[@Fin0] tps).
Definition DoActions_Loop_steps_nil := DoActions_Step_steps_nil.
Fixpoint DoActions_Loop_steps_cons (i : Fin.t n) tps1 tps2 tp := match tps2 with | nil => DoActions_Step_steps_cons i tps1 [] tp | tp' :: tps2' => match finSucc_opt i with | None => 0 (* can't happen *) | Some i' => 1 + DoActions_Step_steps_cons i tps1 tps2 tp + DoActions_Loop_steps_cons i' (tps1 ++ [doAct tp acts[@i]]) tps2' tp' end end.
Definition DoActions_Loop_T (i : Fin.t n) : tRel sigSim 1 := fun tin k => (exists tps1 tps2 tp, (length tps1 =? fin_to_nat i) = true /\ (length tps1 + (1 + length tps2) =? n) = true /\ atCons tin[@Fin0] tps1 tps2 tp /\ DoActions_Loop_steps_cons i tps1 tps2 tp <= k) \/ (exists tps, atNil tin[@Fin0] tps /\ DoActions_Loop_steps_nil <= k).
Definition DoActions_Rel : pRel sigSim unit 1 := ignoreParam (fun tin tout => forall (tps : list (tape sig)), (length tps =? n) = true -> atStart tin[@Fin0] tps -> atNil tout[@Fin0] (map_vect_list (@doAct _) acts tps)).
Definition DoActions : pTM sigSim unit 1 := match finMin_opt n with | None => Move Rmove (* Nothing to do, just move from the start to the nil symbol *) | Some i => Move Rmove;; (* Move from start to first cons *) DoActions_Loop i end.
Definition DoActions_steps (tps : list (tape sig)) : nat := match finMin_opt n with | None => 1 | Some i => match tps with | nil => 0 (* can't happen *) | tp :: tps => 2 + DoActions_Loop_steps_cons i [] tps tp end end.
Definition DoActions_T : tRel sigSim 1 := fun tin k => exists tps, (length tps =? n) = true /\ atStart tin[@Fin0] tps /\ DoActions_steps tps <= k.
End DoActions.
Section Step.
Variable (q : state (projT1 pM)).
Definition Step_Rel : pRel sigSim (state (projT1 pM) + F) 1 := fun tin '(yout, tout) => forall (T : tapes sig n), tin[@Fin0] ≃ T -> if halt q then tout[@Fin0] ≃ T /\ yout = inr (projT2 pM q) else let c := {| cstate := q; ctapes := T |} in let (q', T') := step c in tout[@Fin0] ≃ T' /\ yout = inl q'.
Definition Step : pTM sigSim (state (projT1 pM) + F) 1 := if halt q then Return Nop (inr (projT2 pM q)) else Switch ReadCurrentSymbols (fun (cs : Vector.t (option sig) n) => Return (MoveToStart;; DoActions (snd (trans (q, cs)));; MoveToStart) (inl (fst (trans (q, cs))))).
Definition Step_steps (T : tapes sig n) : nat := let (q', act) := (trans (m := projT1 pM) (q, current_chars T)) in 3 + ReadCurrentSymbols_steps T + MoveToStart_steps (vector_to_list T) + DoActions_steps act (vector_to_list T) + MoveToStart_steps (vector_to_list (doAct_multi T act)).
Definition Step_T : tRel sigSim 1 := fun tin k => if halt q then True else exists (T : tapes sig n), tin[@Fin0] ≃ T /\ Step_steps T <= k.
End Step.
Section Loop.
Definition Loop := StateWhile Step.
Definition Loop_Rel q : pRel sigSim F 1 := fun tin '(yout, tout) => forall (T : tapes sig n), tin[@Fin0] ≃ T -> let c := {| cstate := q; ctapes := T |} in exists c' k, loopM c k = Some c' /\ tout[@Fin0] ≃ ctapes c' /\ yout = projT2 pM (cstate c').
Fixpoint Loop_steps q (T : tapes sig n) (k : nat) {struct k} := if halt q then 0 else match k with | 0 => 0 (* can't happen *) | S k' => let (q', acts) := trans (m := projT1 pM) (q, current_chars T) in 1 + Step_steps q T + Loop_steps q' (doAct_multi T acts) k' end.
Definition Loop_T q : tRel sigSim 1 := fun tin k => exists T kn outc, loopM (mk_mconfig q T) kn = Some outc /\ tin[@Fin0] ≃ T /\ Loop_steps q T kn <= k.
Local Arguments doAct_multi : simpl never.
Definition ToSingleTape := Loop (start (projT1 pM)).
Definition ToSingleTape_Rel := Loop_Rel (start (projT1 pM)).
Definition ToSingleTape_T := Loop_T (start (projT1 pM)).
Variable M_R : pRel sig F n.
Definition ToSingleTape_Rel' : pRel sigSim F 1 := fun tin '(yout, tout) => forall T, tin[@Fin0] ≃ T -> exists T', M_R T (yout, T') /\ tout[@Fin0] ≃ T'.
Variable M_T : tRel sig n.
Definition ToSingleTape_T' : tRel sigSim 1 := fun tin k => exists T k', tin[@Fin0] ≃ T /\ M_T T k' /\ Loop_steps (start (projT1 pM)) T k' <= k.
End Loop.
End ToSingleTape.

Lemma map_vect_list_length (X Y : Type) (f : X -> Y -> X) (n : nat) (vs : Vector.t Y n) (ls : list X) : length (map_vect_list f vs ls) = length ls.
Proof.
revert n vs.
induction ls as [ | x ls IH]; cbn; intros.
-
reflexivity.
-
destruct vs as [ | y n vs]; cbn; f_equal; auto.

From Undecidability.TM Require Import Util.TM_facts.
Section Mk_Mono.
Variable (sig state : finType).
Variable mono_trans : state -> option sig -> state * (option sig * move).
Variable (init : state) (fin : state -> bool).
Definition Mk_Mono_TM : TM sig 1.
Proof.
split with (state := state).
-
intros (q&tape).
pose proof (mono_trans q (tape[@Fin0])) as (q', act).
apply (q', [| act |]).
-
apply init.
-
apply fin.
Defined.
Variable (F : finType) (R : Rel (tape sig) (F * tape sig)).
Definition Mk_R_p : Rel (tapes sig 1) (F * tapes sig 1) := fun tps1 '(p, tps2) => R (tps1[@Fin0]) (p, tps2[@Fin0]).
End Mk_Mono.
Arguments Mk_R_p { sig F } ( R ) x y /.
Section DoAct.
Variable sig : finType.
Variable c : sig.
Variable act : option sig * move.
Definition DoAct_TM := {| trans := fun '(q, sym) => (true, [| act |]); start := false; halt x := x; |}.
Definition DoAct : pTM sig unit 1 := (DoAct_TM; fun _ => tt).
Definition DoAct_Rel : pRel sig unit 1 := Mk_R_p (ignoreParam (fun t t' => t' = doAct t act)).
End DoAct.
Arguments DoAct : simpl never.
Arguments DoAct_Rel { sig } act x y /.
Section DoAct_Derived.
Variable sig : finType.
Variable c : sig.
Variable (D : move).
Definition Write : pTM sig unit 1 := DoAct (Some c, Nmove).
Definition Write_Rel : pRel sig unit 1 := Mk_R_p (ignoreParam (fun t t' => t' = midtape (left t) c (right t))).
Definition Move : pTM sig unit 1 := DoAct (None, D).
Definition Move_Rel : pRel sig unit 1 := Mk_R_p (ignoreParam (fun t t' => t' = tape_move (sig := sig) t D)).
Definition WriteMove : pTM sig unit 1 := DoAct (Some c, D).
Definition WriteMove_Rel : pRel sig unit 1 := Mk_R_p (ignoreParam (fun t t' => t' = tape_move (tape_write t (Some c)) D)).
End DoAct_Derived.
Arguments Write : simpl never.
Arguments Write_Rel { sig } c x y / : rename.
Arguments Move : simpl never.
Arguments Move { sig } D.
Arguments Move_Rel { sig } ( D ) x y /.
Arguments WriteMove : simpl never.
Arguments WriteMove_Rel { sig } (w D) x y / : rename.
Section CaseChar.
Variable sig : finType.
Variable (F : finType) (f : option sig -> F).
Definition CaseChar_TM : TM sig 1 := {| trans := fun '(_, sym) => (Some (f sym[@Fin0]), [| (None, Nmove) |]); start := None; halt := fun s => match s with | None => false | Some _ => true end; |}.
Definition CaseChar : pTM sig F 1 := (CaseChar_TM; fun s => match s with None => f None (* not terminated yet *) | Some y => y end).
Definition CaseChar_Rel : pRel sig F 1 := fun t '(y, t') => y = f (current t[@Fin0]) /\ t' = t.
Definition CaseChar_Sem : CaseChar ⊨c(1) CaseChar_Rel.
Proof.
intros t.
destruct_tapes.
cbn.
unfold initc; cbn.
cbv [step]; cbn.
unfold current_chars; cbn.
eexists (mk_mconfig _ _); cbv [step]; cbn.
split.
eauto.
cbn.
auto.
End CaseChar.
Arguments CaseChar : simpl never.
Arguments CaseChar {sig F} f.
Arguments CaseChar_Rel sig F f x y /.
Section ReadChar.
Variable sig : finType.
Definition ReadChar : pTM sig (option sig) 1 := CaseChar id.
Definition ReadChar_Rel : pRel sig (option sig) 1 := fun t '(y, t') => y = current t[@Fin0] /\ t' = t.
Definition ReadChar_Sem : ReadChar ⊨c(1) ReadChar_Rel.
Proof.
eapply RealiseIn_monotone.
-
apply CaseChar_Sem.
-
reflexivity.
-
intros tin (yout, tout) (->&->).
hnf.
split; auto.
End ReadChar.
Arguments ReadChar : simpl never.
Arguments ReadChar {sig}.
Arguments ReadChar_Rel sig x y /.
Ltac smpl_TM_Mono := once lazymatch goal with | [ |- DoAct _ ⊨ _] => eapply RealiseIn_Realise; eapply DoAct_Sem | [ |- DoAct _ ⊨c(_) _] => eapply DoAct_Sem | [ |- projT1 (DoAct _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply DoAct_Sem | [ |- Write _ ⊨ _] => eapply RealiseIn_Realise; eapply Write_Sem | [ |- Write _ ⊨c(_) _] => eapply Write_Sem | [ |- projT1 (Write _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply Write_Sem | [ |- Move _ ⊨ _] => eapply RealiseIn_Realise; eapply Move_Sem | [ |- Move _ ⊨c(_) _] => eapply Move_Sem | [ |- projT1 (Move _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply Move_Sem | [ |- WriteMove _ _ ⊨ _] => eapply RealiseIn_Realise; eapply WriteMove_Sem | [ |- WriteMove _ _ ⊨c(_) _] => eapply WriteMove_Sem | [ |- projT1 (WriteMove _ _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply WriteMove_Sem | [ |- CaseChar _ ⊨ _] => eapply RealiseIn_Realise; eapply CaseChar_Sem | [ |- CaseChar _ ⊨c(_) _] => eapply CaseChar_Sem | [ |- projT1 (CaseChar _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply CaseChar_Sem | [ |- ReadChar ⊨ _] => eapply RealiseIn_Realise; eapply ReadChar_Sem | [ |- ReadChar ⊨c(_) _] => eapply ReadChar_Sem | [ |- projT1 (ReadChar) ↓ _] => eapply RealiseIn_TerminatesIn; eapply ReadChar_Sem end.
Smpl Add smpl_TM_Mono : TM_Correct.

Definition ReadChar_Sem : ReadChar ⊨c(1) ReadChar_Rel.
Proof.
eapply RealiseIn_monotone.
-
apply CaseChar_Sem.
-
reflexivity.
-
intros tin (yout, tout) (->&->).
hnf.
split; auto.

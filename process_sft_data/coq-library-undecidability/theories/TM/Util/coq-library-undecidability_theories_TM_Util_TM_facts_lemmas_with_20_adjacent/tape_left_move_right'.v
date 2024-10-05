From Undecidability.TM.Util Require Export Prelim Relations.
Require Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Export Undecidability.TM.TM.
Section Fix_Sigma.
Variable sig : Type.
Notation tape := (tape sig).
Definition tapes n := Vector.t tape n.
Definition tapeToList (t : tape) : list sig := match t with | niltape => [] | leftof s r => s :: r | rightof s l => List.rev (s :: l) | midtape l c r => (List.rev l) ++ [c] ++ r end.
Definition sizeOfTape t := |tapeToList t|.
Definition sizeOfmTapes n (v : tapes n) := Vector.fold_left max 0 (Vector.map sizeOfTape v).
Definition left := fun (t : tape) => match t with | niltape => [] | leftof _ _ => [] | rightof s l => s :: l | midtape l _ _ => l end.
Definition right := fun (t : tape) => match t with | niltape => [] | leftof s r => s :: r | rightof _ _ => [] | midtape _ _ r => r end.
Global Instance move_eq_dec : eq_dec move.
Proof.
intros.
hnf.
decide equality.
Defined.
Global Instance move_finC : finTypeC (EqType move).
Proof.
apply (FinTypeC (enum := [Lmove; Rmove; Nmove])).
intros []; now cbv.
Defined.
Definition tape_move_right' ls a rs : tape := match rs with | nil => rightof a ls | r::rs' => midtape (a::ls) r rs' end.
Definition tape_move_right := fun (t : tape) => match t with | niltape => niltape | rightof _ _ =>t | leftof a rs =>midtape [ ] a rs | midtape ls a rs => tape_move_right' ls a rs end.
Definition tape_move_left' ls a rs : tape := match ls with | nil => leftof a rs | l::ls' => midtape ls' l (a::rs) end.
Definition tape_move_left := fun (t : tape) => match t with | niltape => niltape | leftof _ _ => t | rightof a ls => midtape ls a [ ] | midtape ls a rs => tape_move_left' ls a rs end.
Definition tape_move (t : tape) (m : move) := match m with | Rmove => tape_move_right t | Lmove => tape_move_left t | Nmove => t end.
Definition tape_write (t : tape) (s : option sig) := match s with | None => t | Some s' => midtape (left t) s' (right t) end.
Definition doAct (t : tape) (mv : option sig * move) := tape_move (tape_write t (fst mv)) (snd mv).
Definition doAct_multi (n : nat) (ts : tapes n) (actions : Vector.t (option sig * move) n) := Vector.map2 doAct ts actions.
Definition current_chars (n : nat) (tapes : tapes n) := Vector.map current tapes.
End Fix_Sigma.
Ltac destruct_tapes := unfold tapes in *; destruct_vector.
Create HintDb tape.
Create HintDb vector.
Tactic Notation "simpl_tape" := repeat rewrite_strat (topdown (choice (hints tape) (hints vector))).
Tactic Notation "simpl_tape" "in" ident(H) := repeat rewrite_strat (topdown (choice (hints tape) (hints vector))) in H.
Tactic Notation "simpl_tape" "in" "*" := repeat multimatch goal with | [ H : _ |- _ ] => simpl_tape in H end; simpl_tape.
Tactic Notation "simpl_vector" := repeat rewrite_strat (topdown (hints vector)).
Tactic Notation "simpl_vector" "in" ident(H) := repeat rewrite_strat (topdown (hints vector)) in H.
Tactic Notation "simpl_vector" "in" "*" := repeat multimatch goal with | [ H : _ |- _ ] => simpl_vector in H end; simpl_vector.
Hint Rewrite tapeToList_move : tape.
Hint Rewrite tapeToList_move_R : tape.
Hint Rewrite tapeToList_move_L : tape.
Hint Rewrite tape_move_right_left using eauto : tape.
Hint Rewrite tape_move_left_right using eauto : tape.
Arguments current_chars : simpl never.
Hint Unfold current_chars : tape.
Hint Rewrite @nth_map' : vector.
Hint Rewrite @nth_map2' : vector.
Hint Rewrite @nth_tabulate : vector.
Hint Rewrite VectorSpec.const_nth : vector.
Arguments tapes (sig % type) (n % nat).
Section Nop_Action.
Variable n : nat.
Variable sig : finType.
Definition nop_action := Vector.const (@None sig, Nmove) n.
End Nop_Action.
Arguments nop_action {_ _}.
Section MirrorTape.
Variable (n : nat) (sig : Type).
Definition mirror_tape (t : tape sig) : tape sig := match t with | niltape _ => niltape _ | leftof r rs => rightof r rs | rightof l ls => leftof l ls | midtape ls m rs => midtape rs m ls end.
Definition mirror_tapes (t : tapes sig n) : tapes sig n := Vector.map mirror_tape t.
Definition mirror_move (D : move) : move := match D with | Nmove => Nmove | Lmove => Rmove | Rmove => Lmove end.
End MirrorTape.
Arguments mirror_tapes : simpl never.
Hint Unfold mirror_tapes : tape.
Hint Rewrite mirror_tape_left : tape.
Hint Rewrite mirror_tape_right : tape.
Hint Rewrite mirror_tape_current : tape.
Hint Rewrite mirror_tape_involution : tape.
Hint Rewrite mirror_tape_move_left : tape.
Hint Rewrite mirror_tape_move_right : tape.
Hint Rewrite mirror_tapes_involution : tape.
Hint Rewrite mirror_tapes_nth : tape.
Section Tape_Local.
Variable sig : Type.
Definition tape_local (t : tape sig) : list sig := match t with | niltape _ => [] | leftof a l => [] | rightof _ _ => [] | midtape _ a l => a :: l end.
Definition tape_local_l (t : tape sig) : list sig := match t with | niltape _ => [] | leftof a l => [] | rightof _ _ => [] | midtape r a l => a :: r end.
End Tape_Local.
Hint Rewrite tape_local_mirror : tape.
Hint Rewrite tape_local_mirror' : tape.
Hint Rewrite tape_local_current_cons using auto : tape.
Hint Rewrite tape_local_l_current_cons using auto : tape.
Hint Rewrite tape_local_right using auto : tape.
Hint Rewrite tape_local_l_left using auto : tape.
Hint Rewrite tape_left_move_right using auto : tape.
Hint Rewrite tape_right_move_left using auto : tape.
Section MapTape.
Variable sig tau : Type.
Variable g : tau -> sig.
Definition mapTape : tape tau -> tape sig.
Proof.
destruct 1 eqn:E1.
-
apply niltape.
-
apply leftof.
apply (g t).
apply (List.map g l).
-
apply rightof.
apply (g t).
apply (List.map g l).
-
apply midtape.
apply (List.map g l).
apply (g t).
apply (List.map g l0).
Defined.
Definition mapTapes {n : nat} : Vector.t (tape tau) n -> Vector.t (tape sig) n := Vector.map mapTape.
End MapTape.
Hint Rewrite mapTape_current : tape.
Hint Rewrite mapTape_left : tape.
Hint Rewrite mapTape_right : tape.
Hint Rewrite mapTape_move_left : tape.
Hint Rewrite mapTape_move_right : tape.
Hint Unfold mapTapes : tape.
Hint Rewrite mapTape_mapTape : tape.
Hint Rewrite mapTape_id : tape.
Hint Rewrite mapTape_local : tape.
Section MatchTapes.
Variable sig : Type.
End MatchTapes.
Hint Rewrite tape_left_move_left' : tape.
Hint Rewrite tape_left_move_left : tape.
Hint Rewrite tape_left_move_right' : tape.
Hint Rewrite tape_right_move_left' : tape.
Hint Rewrite tape_local_l_move_left' : tape.
Hint Rewrite mirror_tape_move_left' : tape.
Hint Rewrite tape_right_move_right' : tape.
Hint Rewrite tape_right_move_right : tape.
Hint Rewrite tape_right_move_left' : tape.
Hint Rewrite tape_right_move_right' : tape.
Hint Rewrite tape_local_move_right' : tape.
Hint Rewrite mirror_tape_move_right' : tape.
Hint Rewrite tape_move_niltape tape_write_left tape_write_right tape_write_current_Some tape_write_current_None tape_write_current : tape.
Section Semantics.
Variable sig : finType.
Notation TM := (TM sig).
Definition pTM (F: Type) (n:nat) := { M : TM n & state M -> F }.
Record mconfig (state:finType) (n:nat): Type := mk_mconfig { cstate : state; ctapes : tapes sig n }.
Definition step {n} (M:TM n) : mconfig (state M) n -> mconfig (state M) n := fun c => let (news,actions) := trans (cstate c, current_chars (ctapes c)) in mk_mconfig news (doAct_multi (ctapes c) actions).
Definition haltConf {n} (M : TM n) : mconfig (state M) n -> bool := fun c => halt (cstate c).
Definition loopM n (M : TM n) := loop (@step _ M) (@haltConf _ M).
Definition initc n (M : TM n) tapes := mk_mconfig (n := n) (@start _ n M) tapes.
Definition pRel (sig : Type) (F: Type) (n : nat) := Rel (tapes sig n) (F * tapes sig n).
Definition Realise n F (pM : pTM n F) (R : pRel sig n F) := forall t k outc, loopM (initc (projT1 pM) t) k = Some outc -> R t (projT2 pM (cstate outc), ctapes outc).
Notation "M '⊨' R" := (Realise M R) (no associativity, at level 30, format "M '⊨' R").
Definition tRel sig n := Rel (tapes sig n) nat.
Definition TerminatesIn {n : nat} (M : TM n) (T : tRel sig n) := forall tin k, T tin k -> exists conf, loopM (initc M tin) k = Some conf.
Arguments TerminatesIn { _ } _.
Notation "M ↓ T" := (TerminatesIn M T) (no associativity, at level 60, format "M '↓' T").
Definition RealiseIn n (F : Type) (pM : pTM F n) (R : pRel sig F n) (k : nat) := forall input, exists outc, loopM (initc (projT1 pM) input) k = Some outc /\ R input ((projT2 pM (cstate outc)), ctapes outc).
Notation "M '⊨c(' k ')' R" := (RealiseIn M R k) (no associativity, at level 45, format "M '⊨c(' k ')' R").
Section Canonical_Correctness.
Variable (n : nat).
Variable (F : Type).
Variable (pM : pTM F n).
Definition Canonical_Rel : pRel sig F n := fun t1 '(y, t2) => exists outc k, loopM (M := projT1 pM) (initc (projT1 pM) t1) k = Some outc /\ ctapes outc = t2 /\ projT2 pM (cstate outc) = y.
Fact Canonical_Realise : pM ⊨ Canonical_Rel.
Proof.
hnf.
firstorder eauto.
End Canonical_Correctness.
Section Canonical_Termination.
Variable (n : nat).
Variable (M : TM n).
Definition Canonical_T : tRel sig n := fun t k => exists outc, loopM (M := M) (initc M t) k = Some outc.
End Canonical_Termination.
End Semantics.
Notation "'(' M ';' labelling ')'" := (existT (fun x => state x -> _) M labelling).
Notation "M '⊨' R" := (Realise M R) (no associativity, at level 60, format "M '⊨' R").
Notation "M '⊨c(' k ')' R" := (RealiseIn M R k) (no associativity, at level 45, format "M '⊨c(' k ')' R").
Notation "M '↓' t" := (TerminatesIn M t) (no associativity, at level 60, format "M '↓' t").
Instance inhabited_move : inhabitedC move := ltac:(repeat constructor).
Instance inhabited_TM_Q (n : nat) (sig : finType) (M : TM sig n) : inhabitedC (state M).
Proof.
constructor.
apply start.
Hint Extern 4 => once lazymatch goal with | [ pM : pTM ?sig ?F ?n |- inhabitedC ?F ] => apply (inhabited_pTM_lab pM) end : typeclass_instances.
Section Test_def.
Variable (n : nat) (sig : finType) (F : Type).
Variable (pM : pTM sig F n).
Goal let _ := default : state (projT1 pM) in True.
Proof.
exact I.
Goal let _ := default : F in True.
Proof.
exact I.
End Test_def.
Definition execTM (sig : finType) (n : nat) (M : TM sig n) (tapes : tapes sig n) (k : nat) := option_map (@ctapes _ _ _) (loopM (initc M tapes) k).
Definition execTM_p (sig : finType) (n : nat) (F : Type) (pM : { M : TM sig n & state M -> F }) (tapes : tapes sig n) (k : nat) := option_map (fun x => (ctapes x, projT2 pM (cstate x))) (loopM (initc (projT1 pM) tapes) k ).
Smpl Create TM_Correct.
Ltac TM_Correct_step := smpl TM_Correct.
Ltac TM_Correct := repeat TM_Correct_step.

Lemma midtape_tape_local_cons t r2 x : tape_local t = x :: r2 <-> t = midtape (left t) x r2.
Proof.
split.
-
intros H1.
destruct t; cbn in *; congruence.
-
intros H1.
destruct t; cbn in *; inv H1.
Admitted.

Lemma midtape_tape_local_cons_left t r1 r2 x : left t = r1 /\ tape_local t = x :: r2 <-> t = midtape r1 x r2.
Proof.
rewrite midtape_tape_local_cons.
Admitted.

Lemma midtape_tape_local_l_cons t r1 x : tape_local_l t = x :: r1 <-> t = midtape r1 x (right t).
Proof.
split.
-
intros H1.
destruct t; cbn in *; congruence.
-
intros H1.
destruct t; cbn in *; inv H1.
Admitted.

Lemma midtape_tape_local_l_cons_right t r1 r2 x : tape_local_l t = x :: r1 /\ right t = r2 <-> t = midtape r1 x r2.
Proof.
rewrite midtape_tape_local_l_cons.
Admitted.

Definition mapTape : tape tau -> tape sig.
Proof.
destruct 1 eqn:E1.
-
apply niltape.
-
apply leftof.
apply (g t).
apply (List.map g l).
-
apply rightof.
apply (g t).
apply (List.map g l).
-
apply midtape.
apply (List.map g l).
apply (g t).
Admitted.

Lemma mapTape_current t : current (mapTape t) = map_opt g (current t).
Proof.
Admitted.

Lemma mapTape_left t : left (mapTape t) = List.map g (left t).
Proof.
Admitted.

Lemma mapTape_right t : right (mapTape t) = List.map g (right t).
Proof.
Admitted.

Lemma mapTape_move_left t : tape_move_left (mapTape t) = mapTape (tape_move_left t).
Proof.
destruct t; cbn; auto.
Admitted.

Lemma mapTape_move_right t : tape_move_right (mapTape t) = mapTape (tape_move_right t).
Proof.
destruct t; cbn; auto.
Admitted.

Lemma mapTape_inv_niltap t : mapTape t = niltape _ -> t = niltape _.
Proof.
intros.
destruct t; inv H.
Admitted.

Lemma mapTape_inv_rightof t l ls : mapTape t = rightof l ls -> exists l' ls', t = rightof l' ls' /\ l = g l' /\ ls = map g ls'.
Proof.
intros.
destruct t; inv H.
Admitted.

Lemma mapTape_inv_leftof t r rs : mapTape t = leftof r rs -> exists r' rs', t = leftof r' rs' /\ r = g r' /\ rs = map g rs'.
Proof.
intros.
destruct t; inv H.
Admitted.

Lemma mapTape_inv_midtape t ls m rs : mapTape t = midtape ls m rs -> exists ls' m' rs', t = midtape ls' m' rs' /\ ls = map g ls' /\ m = g m' /\ rs = map g rs'.
Proof.
intros.
destruct t; inv H.
Admitted.

Lemma mapTape_mapTape (sig tau gamma : Type) (f : sig -> tau) (g : tau -> gamma) (t : tape sig) : mapTape g (mapTape f t) = mapTape (fun x => g (f x)) t.
Proof.
Admitted.

Lemma mapTape_ext (sig tau : Type) (f g : sig -> tau) (t : tape sig) : (forall a, f a = g a) -> mapTape f t = mapTape g t.
Proof.
intros H.
Admitted.

Lemma mapTape_id (sig : Type) (t : tape sig) : mapTape (fun x => x) t = t.
Proof.
Admitted.

Lemma mapTape_local (sig tau : Type) (f : sig -> tau) t : tape_local (mapTape f t) = List.map f (tape_local t).
Proof.
Admitted.

Lemma tape_left_move_left' ls (x : sig) rs : left (tape_move_left' ls x rs) = tl ls.
Proof.
Admitted.

Lemma tape_left_move_left (t : tape sig) : left (tape_move_left t) = tl (left t).
Proof.
destruct t; cbn; auto.
Admitted.

Lemma tape_right_move_left' ls (x : sig) rs : right (tape_move_left' ls x rs) = x :: rs.
Proof.
Admitted.

Lemma tape_local_l_move_left' rs (x : sig) ls : tape_local_l (tape_move_left' rs x ls) = rs.
Proof.
Admitted.

Lemma mirror_tape_move_left' rs (x : sig) ls : mirror_tape (tape_move_left' rs x ls) = tape_move_right' ls x rs.
Proof.
Admitted.

Lemma tape_right_move_right' ls (x : sig) rs : right (tape_move_right' ls x rs) = tl rs.
Proof.
Admitted.

Lemma tape_right_move_right (t : tape sig) : right (tape_move_right t) = tl (right t).
Proof.
destruct t; cbn; auto.
Admitted.

Lemma tape_local_move_right' rs (x : sig) ls : tape_local (tape_move_right' rs x ls) = ls.
Proof.
Admitted.

Lemma mirror_tape_move_right' rs (x : sig) ls : mirror_tape (tape_move_right' rs x ls) = tape_move_left' ls x rs.
Proof.
Admitted.

Lemma tape_move_niltape (m : move) : tape_move (niltape sig) m = niltape sig.
Proof.
Admitted.

Lemma tape_write_left (t : tape sig) s : left (tape_write t s) = left t.
Proof.
Admitted.

Lemma tape_write_right (t : tape sig) s : right (tape_write t s) = right t.
Proof.
Admitted.

Lemma tape_write_current_Some (t : tape sig) s : current (tape_write t (Some s)) = Some s.
Proof.
Admitted.

Lemma tape_write_current_None (t : tape sig) : current (tape_write t None) = current t.
Proof.
Admitted.

Lemma tape_write_current (t : tape sig) s : current (tape_write t s) = fold_opt (@Some _) (current t) s.
Proof.
Admitted.

Lemma Realise_monotone n (F : Type) (pM : pTM F n) R R' : pM ⊨ R' -> R' <<=2 R -> pM ⊨ R.
Proof.
Admitted.

Lemma TerminatesIn_monotone {n : nat} (M : TM n) (T T' : tRel sig n) : M ↓ T' -> (T <<=2 T') -> M ↓ T.
Proof.
intros H1 H2.
Admitted.

Lemma TerminatesIn_extend {n : nat} (M : TM n) (T : tRel sig n) : M ↓ T -> M ↓ (fun tin k => exists k', k' <= k /\ T tin k').
Proof.
intros HTerm.
hnf in *.
intros tin k.
intros (k'&Hk'&HT).
specialize HTerm with (1 := HT) as (oconf&HLoop).
exists oconf.
Admitted.

Lemma RealiseIn_monotone n (F : Type) (pM : pTM F n) (R R' : pRel sig F n) k k' : pM ⊨c(k') R' -> k' <= k -> R' <<=2 R -> pM ⊨c(k) R.
Proof.
unfold RealiseIn.
intros H1 H2 H3 input.
specialize (H1 input) as (outc & H1).
exists outc.
split.
-
unfold loopM.
eapply loop_monotone; eauto.
intuition.
-
Admitted.

Lemma RealiseIn_monotone' n (F : Type) (pM : pTM F n) (R : pRel sig F n) k k' : pM ⊨c(k') R -> k' <= k -> pM ⊨c(k) R.
Proof.
intros H1 H2.
eapply RealiseIn_monotone.
eapply H1.
assumption.
Admitted.

Lemma RealiseIn_split n (F : Type) (pM : pTM F n) R1 R2 (k : nat) : pM ⊨c(k) R1 /\ pM ⊨c(k) R2 <-> pM ⊨c(k) R1 ∩ R2.
Proof.
split; swap 1 2; [ intros H | intros (H1&H2)]; repeat intros ?.
hnf; firstorder eauto.
specialize (H1 input) as (outc &H1&H1').
specialize (H2 input) as (outc2&H2&H2').
pose proof loop_injective H1 H2 as <-.
exists outc.
Admitted.

Lemma Realise_total n (F : Type) (pM : { M : TM n & state M -> F }) R k : pM ⊨ R /\ projT1 pM ↓ (fun _ i => k <= i) <-> pM ⊨c(k) R.
Proof.
split.
-
intros (HR & Ht) t.
edestruct (Ht t k).
cbn; lia.
eauto.
-
intros H.
split.
+
intros t i cout Hc.
destruct (H t) as (? & ? & ?).
replace cout with x.
eassumption.
unfold loopM in *.
eapply loop_injective; eauto.
+
intros t i Hi.
edestruct (H t) as (? & ? & ?).
exists x.
Admitted.

Lemma tape_left_move_right' ls (x : sig) rs : left (tape_move_right' ls x rs) = x :: ls.
Proof.
destruct rs; cbn; reflexivity.

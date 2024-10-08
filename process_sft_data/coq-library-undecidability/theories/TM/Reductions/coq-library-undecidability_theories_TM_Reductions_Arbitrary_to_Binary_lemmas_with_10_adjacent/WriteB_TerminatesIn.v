From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import ArithPrelim.
Require Import Undecidability.Shared.FinTypeEquiv Undecidability.Shared.FinTypeForallExists.
Set Default Proof Using "Type".
Section fix_Sigma.
Variable n : nat.
Definition encode_sym (s : Fin.t n) : list bool := let i := proj1_sig (Fin.to_nat s) in repeat false i ++ repeat true (n - i).
Fixpoint encode_string (s : list (Fin.t n)) := match s with | [] => [] | i :: l => false :: encode_sym i ++ true :: encode_string l end.
Definition encode_tape (t : tape (Fin.t n)) := match t with | niltape => niltape | midtape ls c_i rs => midtape (rev (encode_string (rev ls))) false (encode_sym c_i ++ true :: encode_string rs) | leftof c_i rs => leftof false (encode_sym c_i ++ true :: encode_string rs) | rightof c_i ls => rightof true (rev (encode_sym c_i) ++ false :: rev(encode_string (rev (ls)))) end.
End fix_Sigma.
Fixpoint ReadB (n : nat) : pTM (FinType (EqType bool)) (option (Fin.t n)) 1.
Proof.
destruct n as [ | n ].
-
exact (Return Nop None).
-
refine (Switch ReadChar (fun o : option bool => match o with None => Return Nop None | Some _ => Move Rmove ;; Switch ReadChar (fun o : option bool => match o with | None => Return (Move Lmove) None | Some true => Return (Move Lmove) (Some Fin.F1) | Some false => Switch (ReadB n) (fun o => Return (Move Lmove) (match o with | None => None | Some i => Some (Fin.R 1 i) end)) end) end)).
Defined.
Definition ReadB_rel' d n : Vector.t (tape bool) 1 -> option (Fin.t (d + n)) * Vector.t (tape bool) 1 -> Prop := fun t '(l, t') => forall t_sig : tape (Fin.t n), t = [| encode_tape t_sig |] -> t' = t /\ forall s, current t_sig = Some s -> l = Some (Fin.R d s).
Smpl Add eassumption : TM_Correct.
Fixpoint ReadB_canonical n : {Rel | ReadB n ⊨ Rel}.
Proof.
destruct n; cbn.
-
eexists.
TM_Correct.
-
eexists.
eapply Switch_Realise.
TM_Correct.
cbn in *.
intros [ | ].
instantiate (1 := fun o => match o with None => _ | Some _ => _ end).
eapply Seq_Realise.
TM_Correct.
eapply Switch_Realise.
TM_Correct.
cbn in *.
intros [[] | ].
instantiate (1 := fun o => match o with None => _ | Some true => _ | Some false => _ end).
cbn in *.
TM_Correct.
eapply Switch_Realise.
eapply (proj2_sig (ReadB_canonical n)).
instantiate (1 := fun o => match o with None => _ | Some _ => _ end).
intros []; TM_Correct.
TM_Correct.
cbn.
TM_Correct.
Defined.
Definition isTotal {Σ} {L} {n} (M : pTM Σ L n) := exists c, projT1 M ↓ fun t k => c <= k.
Ltac help := intros;TMSimp; destruct_tapes; TMSimp; try lia; try match goal with [ |- ?L <= ?R ] => tryif (is_evar R) then (eapply le_plus_l) else (ring_simplify; shelve) | _ => idtac end.
Require Import Undecidability.TM.Compound.WriteString.
Fixpoint MoveM {Σ : finType} (D : move) (n : nat) : pTM Σ unit 1 := match n with | 0 => Nop | S n => MoveM D n ;; Move D end.
Definition TestLeftof {Σ : finType} : pTM Σ bool 1 := Switch ReadChar (fun s1 => match s1 with Some _ => Return Nop false | None => Move Rmove ;; Switch ReadChar (fun s2 => match s2 with None => Return Nop false | Some _ => Return (Move Lmove) true end) end).
Definition MoveL_rel {Σ : finType} D (n : nat) : Vector.t (tape Σ) 1 -> unit * Vector.t (tape Σ) 1 -> Prop := fun t '(_, t') => t' = Vector.map (Nat.iter n (fun t => @tape_move Σ t D)) t.
Definition WriteB (n : nat) (c : option (Fin.t n)) : pTM (FinType (EqType bool)) unit 1 := match c with | None => Nop | Some c => Switch TestLeftof (fun b => if b then WriteString Lmove (rev (false :: encode_sym c ++ [true])) else WriteString Rmove (false :: encode_sym c ++ [true]) ;; MoveM Lmove (S n)) end.
Definition MoveB (m : move) n : pTM (finType_CS bool) unit 1 := Switch TestLeftof (fun b => match b, m with | true, Rmove => Move Rmove | _, _ => MoveM m (2 + n) end).
Arguments Nat.iter : simpl never.
Opaque Nat.iter.
Section FixM.
Variable Σ : finType.
Let n := (projT1 (finite_n Σ)).
Let f := (projT1 (projT2 (finite_n Σ))).
Let g := (proj1_sig (projT2 (projT2 (finite_n Σ)))).
Let Hf := (proj1 (proj2_sig (projT2 (projT2 (finite_n Σ))))).
Let Hg := (proj2 (proj2_sig (projT2 (projT2 (finite_n Σ))))).
Instance R : Retract (Fin.t n) Σ.
Proof.
eapply (@Build_Retract _ _ g (fun x => Some (f x ))).
econstructor.
-
intros [= <-]; now rewrite Hg.
-
intros ->; now rewrite Hf.
Definition encode_tape' (t : tape Σ) : tape bool := encode_tape (mapTape f t).
Variable M : TM Σ 1.
Definition Step (q : state M) : pTM (finType_CS bool) (state M + state M) 1 := Switch (ReadB n) (fun c_i => if halt q then Return Nop (inr q) else let '(q', e) := trans M (q, [| map_opt g c_i |]) in let '(existT _ (c', m) _) := destruct_vector_cons e in WriteB (map_opt f c') ;; MoveB m n ;; Return Nop (inl q')).
Smpl Add (eapply ReadB_Realise') : TM_Correct.
Smpl Add (eapply WriteB_Realise') : TM_Correct.
Smpl Add (eapply MoveB_Realise') : TM_Correct.
End FixM.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts Undecidability.TM.Util.TM_facts.
From Equations Require Import Equations.

Lemma ReadB_Realise n : ReadB n ⊨ fun t '(l, t') => forall t_sig : tape (Fin.t n), t = [| encode_tape t_sig |] -> t' = t /\ l = current t_sig.
Proof.
eapply Realise_monotone.
exact (proj2_sig (ReadB_canonical n)).
pose (Rel := (fun n (t : Vector.t _ 1) '(l, t') => match t with | [| midtape ls _ rs |] => forall rs' (c_i : Fin.t n), rs = encode_sym c_i ++ rs' -> t' = t /\ l = Some c_i | _ => t' = t /\ l = None end) : forall n, Vector.t (tape bool) 1 -> option (Fin.t n) * Vector.t (tape bool) 1 -> Prop).
transitivity (Rel n).
-
induction n.
+
subst Rel.
cbn.
intros tp (l, t') (-> & [ _ ->]).
eapply Vector.caseS' with (v := tp).
clear tp.
intros t nl.
eapply Vector.case0 with (v := nl).
clear nl.
destruct t; eauto.
intros rs' c_i ->.
inv c_i.
+
intros t (l, t') (? & tright & (-> & ->) & H).
destruct_tapes.
cbn in *.
rename h into t'.
rename h0 into t.
destruct t; cbn in *.
*
destruct H as (-> & [] & ->).
eauto.
*
destruct H as (-> & [] & ->).
eauto.
*
destruct H as (-> & [] & ->).
eauto.
*
intros rs' c_i ->.
destruct H as ([] & tps & ? & ? & tps' & [-> ->] & H0).
destruct_tapes.
cbn in *.
subst.
rename l0 into ls.
cbn in *.
revert H0.
eapply Fin.caseS' with (p := c_i); clear c_i.
--
cbn.
intros (-> & [] & ->).
eauto.
--
intros c_i.
change (Fin.FS c_i) with (Fin.R 1 c_i) in *.
unfold encode_sym.
cbn in *.
pose proof (Fin.R_sanity 1 c_i) as E.
cbn in E.
rewrite E.
clear E.
cbn.
intros (o & tout & ? & ?).
eapply IHn in H.
cbn in H.
destruct (H _ _ eq_refl) as [-> ->].
cbn in *.
destruct H0 as (-> & [] & ->).
eauto.
-
intros t (l, t').
unfold Rel.
intros H.
destruct_tapes.
rename h0 into t.
rename h into t'.
intros t_sig [= ->].
Admitted.

Lemma ReadB_total n : isTotal (ReadB n).
Proof.
induction n.
-
cbn.
eexists.
eapply TerminatesIn_monotone.
TM_Correct.
intros ? ? H.
exact H.
-
destruct IHn as [c IH].
eexists.
eapply TerminatesIn_monotone.
cbn.
eapply Switch_TerminatesIn.
TM_Correct.
TM_Correct.
intros [].
instantiate (1 := fun f => if f then _ else _).
cbn.
instantiate (1 := ltac:(clear f; refine _)).
eapply Seq_TerminatesIn.
TM_Correct.
TM_Correct.
eapply Switch_TerminatesIn.
TM_Correct.
TM_Correct.
intros [].
instantiate (1 := fun f => match f with Some true => _ | Some false => _ | None => _ end).
cbn.
destruct b0 as [[] | ].
+
cbn.
instantiate (1 := ltac:(clear f b0; refine _)).
TM_Correct.
+
instantiate (1 := ltac:(clear f b0; refine _)).
eapply Switch_TerminatesIn.
eapply ReadB_Realise.
eassumption.
intros [].
cbn.
TM_Correct.
instantiate (1 := fun f => if f then _ else _).
cbn.
instantiate (1 := ltac:(clear f; refine _)).
TM_Correct.
cbn.
instantiate (1 := ltac:(clear f; refine _)).
TM_Correct.
+
cbn.
instantiate (1 := ltac:(clear f; refine _)).
TM_Correct.
+
cbn.
instantiate (1 := ltac:(clear f; refine _)).
TM_Correct.
+
cbn.
intros ? ? ?.
exists 1.
eexists.
split.
lia.
split.
2:{
intros.
TMSimp.
destruct_tapes.
TMSimp.
destruct (current _).
*
exists 1.
eexists.
split.
lia.
split.
2:{
intros.
TMSimp.
destruct_tapes.
TMSimp.
exists 1.
eexists.
split.
lia.
split.
2:{
intros.
TMSimp.
destruct_tapes.
TMSimp.
destruct current.
destruct b0.
instantiate (1 := S _).
lia.
2:lia.
exists c.
eexists.
split.
lia.
split.
2:{
intros.
destruct yout.
instantiate (1 := S _).
lia.
lia.
}
ring_simplify.
shelve.
}
ring_simplify.
shelve.
}
ring_simplify.
cbn.
shelve.
*
shelve.
}
shelve.
Unshelve.
2:exact 0.
4: exact (S c).
all: try lia.
2:{
eapply H.
Admitted.

Lemma TestLeftof_Realise {Σ : finType} : @TestLeftof Σ ⊨ fun t '(b, t') => t = t' /\ match t with [| leftof _ _ |] => b = true | _ => b = false end.
Proof.
eapply Realise_monotone.
unfold TestLeftof.
TM_Correct.
intros t (b, t') ?.
TMSimp.
destruct_tapes.
TMSimp.
rename t_0 into t.
Admitted.

Lemma MoveM_Realise {Σ : finType} D (n : nat) : @MoveM Σ D n ⊨ MoveL_rel D n.
Proof.
induction n; unfold MoveL_rel; cbn.
-
eapply Realise_monotone.
TM_Correct.
intros t ([], t') ->.
destruct_tapes.
reflexivity.
-
eapply Realise_monotone.
eapply Seq_Realise.
eassumption.
TM_Correct.
intros t ([], t') ?; cbn in *.
TMSimp.
destruct_tapes.
TMSimp.
Admitted.

Lemma Nat_iter_S' {A} (f : A -> A) (a : A) n : Nat.iter (S n) f a = f (Nat.iter n f a).
Proof.
Admitted.

Lemma Nat_iter_S {A} (f : A -> A) (a : A) n : Nat.iter (S n) f a = Nat.iter n f (f a).
Proof.
induction n in a |- *; cbn.
-
reflexivity.
-
unfold Nat.iter in IHn.
Admitted.

Lemma Nat_iter_id {A} (a : A) n : Nat.iter n (fun a : A => a) a = a.
Proof.
induction n in a |- *; cbn.
-
reflexivity.
-
unfold Nat.iter in IHn.
Admitted.

Lemma WriteString_MoveBack {Σ : finType} (x : Σ) l : (WriteString Rmove (x :: l) ;; MoveM Lmove (|l|)) ⊨ fun t '(_, t') => t' = Vector.map (fun t => midtape (left t) x (l ++ skipn (|l|) (right t))) t.
Proof.
eapply Realise_monotone.
TM_Correct.
eapply RealiseIn_Realise, WriteString_Sem.
eapply MoveM_Realise.
intros t ([], t') ([] & t1 & ? & ?).
TMSimp.
destruct_tapes.
TMSimp.
f_equal.
rename t_0 into t.
induction l in x, t |- *.
-
reflexivity.
-
cbn [length plus].
rewrite Nat_iter_S'.
rewrite WriteString_Fun_eq.
rewrite IHl.
clear.
destruct t; cbn.
+
now rewrite skipn_nil.
+
reflexivity.
+
now rewrite skipn_nil.
+
unfold tape_move_left'.
unfold tape_move_right'.
cbn.
destruct l1; cbn.
*
now rewrite skipn_nil.
*
Admitted.

Lemma WriteB_Realise (n : nat) (c : option (Fin.t n)) : WriteB c ⊨ fun t '(_, t') => forall t_sig, t = [| encode_tape t_sig |] -> t' = [| encode_tape (wr c t_sig) |].
Proof.
destruct c as [c | ].
-
eapply Realise_monotone.
unfold WriteB.
eapply Switch_Realise.
eapply TestLeftof_Realise.
intros [].
instantiate (1 := fun b => if b then _ else _).
cbn.
eapply RealiseIn_Realise, WriteString_Sem.
pose proof (@WriteString_MoveBack (finType_CS bool) false (encode_sym c ++ [true])).
cbn in H.
replace (|encode_sym c ++ [true]|) with (S n) in H.
2:rewrite app_length, length_encode_sym; cbn; lia.
cbn.
eapply H.
intros t ([], t') ? ? ->.
TMSimp.
destruct_tapes.
TMSimp.
f_equal.
destruct t_sig eqn:E; cbn - [skipn].
+
cbn in *.
TMSimp.
now rewrite app_nil_r.
+
cbn in *.
TMSimp.
generalize (encode_sym t ++ true :: encode_string l).
clear.
intros.
replace (encode_sym c ++ true :: false :: l) with ((encode_sym c ++ [true]) ++ false :: l).
generalize (encode_sym c ++ [true]).
generalize false.
intros.
generalize b at 1 4.
intros.
induction l0 in b0, b, l |- * using rev_ind; cbn.
*
reflexivity.
*
rewrite rev_app_distr.
cbn.
rewrite WriteString_Fun_eq.
destruct l0 as [ | x0 l0 _] using rev_ind.
--
cbn.
reflexivity.
--
rewrite rev_app_distr.
cbn.
rewrite <- !app_assoc.
specialize (IHl0 (b0 :: l) b x).
rewrite rev_app_distr in IHl0.
cbn in *.
rewrite <- app_assoc in IHl0.
cbn in IHl0.
eassumption.
*
now rewrite <- app_assoc.
+
cbn in *.
TMSimp.
rewrite <- app_assoc.
cbn.
repeat f_equal.
rewrite encode_string_app.
cbn.
rewrite !rev_app_distr.
cbn.
rewrite rev_app_distr.
cbn.
now rewrite <- app_assoc.
+
cbn in *.
TMSimp.
rewrite <- app_assoc.
cbn -[skipn].
repeat f_equal.
replace (encode_sym t ++ true :: encode_string l0) with ((encode_sym t ++ [true]) ++ encode_string l0).
pose proof (length_encode_sym t).
destruct (encode_sym) eqn:E.
*
cbn in *.
subst.
reflexivity.
*
cbn in *.
inv H.
rewrite skipn_app.
reflexivity.
rewrite app_length.
cbn.
lia.
*
now rewrite <- app_assoc.
-
cbn.
eapply Realise_monotone.
TM_Correct.
intros t ([], t') ->.
Admitted.

Lemma MoveM_isTotal {Σ : finType} D (n : nat) : isTotal (@MoveM Σ D n).
Proof.
induction n; cbn.
-
eexists.
TM_Correct.
-
destruct IHn as [c IH].
eexists.
eapply TerminatesIn_monotone.
TM_Correct.
eapply MoveM_Realise.
intros ? ? ?.
repeat eexists.
eapply le_plus_l.
cbn.
2: intros; eapply le_plus_l.
eapply H.
Unshelve.
Admitted.

Lemma midtape_left_midtape {Σ : finType} (l1 l2 : list Σ) m m' r n : n = S (length l1) -> Nat.iter n (@tape_move_left Σ) (midtape (rev l1 ++ [m'] ++ l2) m r) = midtape l2 m' (l1 ++ m :: r).
Proof.
intros ->.
induction l1 in m, m', l2 |- *.
-
cbn.
reflexivity.
-
cbn.
rewrite <- app_assoc.
rewrite Nat_iter_S'.
Admitted.

Lemma midtape_right_midtape {Σ : finType} l m r1 c r2 n : n = S (length r1) -> Nat.iter n (@tape_move_right Σ) (midtape l m (r1 ++ c :: r2)) = midtape (rev r1 ++ m :: l) c r2.
Proof.
intros ->.
induction r1 in m, c, r2 |- * using rev_ind; cbn.
-
reflexivity.
-
rewrite app_length.
cbn.
rewrite plus_comm.
cbn.
rewrite <- app_assoc, Nat_iter_S'.
cbn.
rewrite (IHr1 m x (c :: r2)).
cbn.
Admitted.

Lemma midtape_right_rightof {Σ : finType} l m rs c n : n = 2 + (length rs) -> Nat.iter n (@tape_move_right Σ) (midtape l m (rs ++ [c])) = rightof c (rev rs ++ m :: l).
Proof.
intros ->.
cbn.
rewrite Nat_iter_S'.
rewrite midtape_right_midtape.
2:reflexivity.
cbn.
Admitted.

Lemma MoveB_Realise (n : nat) m : MoveB m n ⊨ fun t '(l, t') => forall t_sig, t = [| encode_tape t_sig |] -> t' = [| @encode_tape n (mv m t_sig) |].
Proof.
epose (R := _).
eapply Realise_monotone.
{
unfold MoveB.
eapply Switch_Realise.
eapply TestLeftof_Realise.
instantiate (1 := R m).
subst R.
instantiate (1 := fun m b => if b then _ else _).
cbn.
intros [].
cbn.
instantiate (1 := match m0 with Rmove => _ | _ => _ end).
cbn.
destruct m.
TM_Correct.
eapply MoveM_Realise.
TM_Correct.
TM_Correct.
eapply MoveM_Realise.
TM_Correct.
eapply MoveM_Realise.
}
subst R.
assert (forall n c rs, Nat.iter n (fun t : tape bool => tape_move_left t) (leftof c rs) = leftof c rs) as Eleft.
{
clear.
intros.
clear.
induction n; cbn.
reflexivity.
rewrite Nat_iter_S', IHn.
reflexivity.
}
intros t ([], t') ? t_sig ->.
TMSimp.
destruct_tapes.
f_equal.
destruct t_sig.
-
TMSimp.
destruct_tapes.
TMSimp.
assert (Nat.iter n (fun t : tape bool => tape_move t m) niltape = niltape) as ->.
{
induction n; cbn.
reflexivity.
rewrite Nat_iter_S', IHn.
now destruct m.
}
now destruct m.
-
cbn in *.
TMSimp.
destruct m.
+
TMSimp.
destruct_tapes.
TMSimp.
now rewrite Eleft.
+
TMSimp.
reflexivity.
+
TMSimp.
destruct_tapes.
TMSimp.
now rewrite Nat_iter_id.
-
TMSimp.
destruct_tapes.
TMSimp.
destruct m.
+
cbn.
rewrite <- !Nat_iter_S' with (f := fun t0 => tape_move_left t0).
rewrite Nat_iter_S.
cbn.
pose proof (@midtape_left_midtape (finType_CS bool)).
cbn in H.
erewrite <- H.
2: reflexivity.
rewrite Nat_iter_S'.
rewrite length_encode_sym.
reflexivity.
+
enough (forall c rs, Nat.iter n (fun t : tape bool => tape_move_right t) (rightof c rs) = rightof c rs) as -> by reflexivity.
intros.
clear.
induction n; cbn.
reflexivity.
rewrite Nat_iter_S', IHn.
reflexivity.
+
now rewrite Nat_iter_id.
-
TMSimp.
destruct_tapes.
TMSimp.
rename l into rs, l0 into ls.
rewrite <- !Nat_iter_S' with (f := fun t0 => tape_move t0 m).
destruct m.
+
cbn.
destruct rs.
*
cbn.
rewrite Nat_iter_S.
cbn.
now rewrite Eleft.
*
cbn.
pose proof (@midtape_left_midtape (finType_CS bool)).
cbn in H.
rewrite encode_string_app, rev_app_distr.
cbn.
rewrite rev_app_distr.
cbn.
rewrite Nat_iter_S.
cbn.
rewrite <- app_assoc.
erewrite <- H.
2:reflexivity.
rewrite length_encode_sym.
reflexivity.
+
cbn.
destruct ls.
*
cbn.
pose proof (@midtape_right_rightof (finType_CS bool)).
cbn in H.
rewrite H.
2:now rewrite length_encode_sym.
reflexivity.
*
cbn.
rewrite Nat_iter_S'.
pose proof (@midtape_right_midtape (finType_CS bool)).
cbn in H.
rewrite H.
cbn.
rewrite encode_string_app.
cbn.
rewrite !rev_app_distr.
cbn.
rewrite rev_app_distr.
cbn.
rewrite <- app_assoc.
cbn.
reflexivity.
now rewrite length_encode_sym.
+
cbn.
rewrite Nat_iter_id.
Admitted.

Lemma TestLeftof_total {Σ} : isTotal (@TestLeftof Σ).
Proof.
unfold TestLeftof.
eexists.
eapply TerminatesIn_monotone.
TM_Correct.
intros ? ? ?.
repeat eexists; help.
destruct current; help.
repeat eexists.
help.
help.
help.
instantiate (1 := ltac:(destruct x; refine _)).
cbn.
eapply le_plus_l.
help.
destruct current.
help.
help.
Unshelve.
all: try destruct x; cbn.
4:{
eapply H.
}
Admitted.

Lemma MoveB_total (n : nat) : exists c, forall m, projT1 (MoveB m n) ↓ fun t k => c <= k.
Proof.
destruct (@TestLeftof_total (finType_CS bool)) as [c Hlo].
destruct (@MoveM_isTotal (finType_CS bool) Lmove n) as [c1 H1].
destruct (@MoveM_isTotal (finType_CS bool) Nmove n) as [c2 H2].
destruct (@MoveM_isTotal (finType_CS bool) Rmove n) as [c3 H3].
eexists.
intros m.
eapply TerminatesIn_monotone.
unfold MoveB.
eapply Switch_TerminatesIn.
TM_Correct.
eapply TestLeftof_Realise.
eapply Hlo.
intros f.
instantiate (1 := fun f => if f then _ else _).
cbn.
destruct f.
-
destruct m.
instantiate (1 := ltac:(destruct m, f; refine _)).
all: cbn.
eapply Seq_TerminatesIn.
TM_Correct.
eapply MoveM_Realise.
TM_Correct.
eapply MoveM_Realise.
TM_Correct.
TM_Correct.
TM_Correct.
eapply MoveM_Realise.
eapply MoveM_Realise.
-
instantiate (1 := ltac:(destruct f; refine _)); cbn.
TM_Correct.
eapply MoveM_Realise.
eapply MoveM_Realise.
destruct m.
instantiate (1 := ltac:(destruct m; refine _)); cbn.
all: cbn.
all:eassumption.
-
cbn.
intros ? ? ?.
repeat eexists; help.
TMSimp.
destruct_tapes.
TMSimp.
rename tout_0 into h.
destruct h; TMSimp.
repeat eexists; help.
destruct m.
instantiate (1:= ltac:(destruct m; refine _)); cbn.
all:cbn.
all:help.
destruct m.
instantiate (1:= ltac:(destruct m; refine _)); cbn.
all:cbn.
repeat eexists; help.
lia.
repeat eexists; help.
repeat eexists.
destruct m.
instantiate (1:= ltac:(destruct m; refine _)); cbn.
all:cbn.
all:help.
repeat eexists.
destruct m.
instantiate (1:= ltac:(destruct m; refine _)); cbn.
all:cbn.
all:help.
Unshelve.
all: try destruct x; cbn in *.
all: try destruct x; cbn in *.
all:try destruct m; cbn in *.
17:{
eapply H.
}
16:{
instantiate (6 := c1).
instantiate (6 := c3) in H.
ring_simplify in H.
ring_simplify.
replace (c + c1 + c3) with (c + c3 + c1) by lia.
eapply H.
}
14:{
ring_simplify.
ring_simplify in H.
instantiate (6 := c3).
instantiate (5 := c1).
instantiate (5 := c2) in H.
replace (c + c3 + c2 + c1) with (c + c3 + c1 + c2) by lia.
eapply H.
}
all:try exact 0.
all: try lia.
Admitted.

Instance R : Retract (Fin.t n) Σ.
Proof.
eapply (@Build_Retract _ _ g (fun x => Some (f x ))).
econstructor.
-
intros [= <-]; now rewrite Hg.
-
Admitted.

Lemma ReadB_Realise' : ReadB n ⊨ fun t '(l, t') => forall t_sig : tape Σ, t = [| encode_tape' t_sig |] -> t' = t /\ l = map_opt f (current t_sig).
Proof.
eapply Realise_monotone.
eapply ReadB_Realise.
intros t (?, t') ? t_sig ->.
destruct_tapes.
cbn in *.
specialize (H (mapTape f t_sig) eq_refl) as [[= ->] ->].
split.
eauto.
Admitted.

Lemma WriteB_Realise' (c : option Σ) : WriteB (map_opt f c) ⊨ fun t '(_, t') => forall t_sig, t = [| encode_tape' t_sig |] -> t' = [| encode_tape' (wr c t_sig) |].
Proof.
eapply Realise_monotone.
eapply WriteB_Realise.
intros t (?, t') ? t_sig ->.
destruct_tapes.
cbn in *.
specialize (H (mapTape f t_sig) eq_refl) as [= ->].
unfold tape_write.
destruct c.
-
cbn.
destruct t_sig; reflexivity.
-
Admitted.

Lemma MoveB_Realise' m : MoveB m n ⊨ fun t '(l, t') => forall t_sig, t = [| encode_tape' t_sig |] -> t' = [| encode_tape' (mv m t_sig) |].
Proof.
eapply Realise_monotone.
eapply MoveB_Realise.
intros t (?, t') ? t_sig ->.
destruct_tapes.
cbn in *.
specialize (H (mapTape f t_sig) eq_refl) as [= ->].
f_equal.
destruct t_sig, m; try reflexivity.
cbn.
destruct l; cbn; reflexivity.
cbn.
Admitted.

Lemma WriteB_TerminatesIn (n : nat) (c : option (Fin.t n)) : isTotal (WriteB c).
Proof.
destruct (@MoveM_isTotal (finType_CS bool) Lmove n) as [MoveM_c H_MoveM].
red.
eexists.
eapply TerminatesIn_monotone.
unfold WriteB.
destruct c; cbn.
-
instantiate (1 := ltac:(destruct c; refine _ )).
cbn.
TM_Correct.
eapply TestLeftof_Realise.
unfold TestLeftof.
TM_Correct.
eapply RealiseIn_TerminatesIn, WriteString_Sem.
eapply RealiseIn_Realise, WriteString_Sem.
eapply RealiseIn_TerminatesIn, WriteString_Sem.
eapply MoveM_Realise.
-
cbn.
TM_Correct.
-
cbn.
intros ? ? ?.
destruct c; cbn.
+
repeat eexists.
help.
eapply le_plus_l.
intros.
TMSimp.
destruct_tapes.
cbn.
destruct (current _).
*
destruct b; help.
*
repeat eexists.
help.
help.
help.
eapply le_plus_l.
intros.
TMSimp.
destruct_tapes.
TMSimp.
destruct current.
destruct b; help.
lia.
*
eapply H.
*
intros.
TMSimp.
destruct_tapes.
rename tout_0 into h.
destruct h; help.
--
TMSimp.
repeat eexists.
rewrite !app_length, length_encode_sym.
cbn.
eapply le_plus_l.
cbn.
instantiate (1 := ltac:(destruct c; refine _ )).
cbn in *.
eapply le_plus_l.
eapply le_plus_l.
eapply le_plus_l.
intros.
eapply le_plus_l.
--
TMSimp.
rewrite !app_length, rev_length, !app_length, length_encode_sym.
cbn.
lia.
--
TMSimp.
repeat eexists.
rewrite !app_length, length_encode_sym.
cbn.
eapply le_plus_l.
2: eapply le_plus_l.
2:eapply le_plus_l.
2: intros; eapply le_plus_l.
ring_simplify.
shelve.
--
TMSimp.
repeat eexists.
rewrite !app_length, length_encode_sym.
cbn.
eapply le_plus_l.
cbn.
shelve.
eapply le_plus_l.
eapply le_plus_l.
intros.
eapply le_plus_l.
+
lia.
Unshelve.
all: try exact 0.
lia.
lia.
lia.
